use std::fmt::{Debug, Display};

use itertools::Itertools;
use log::info;

use crate::data_structures::InverseMap;

use super::{Constant, LinearProgram, Operation, Program, TypeSystemBounds};

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct TestCase {
    pub inputs: Vec<Constant>,
    pub output: Constant,
}

impl Display for TestCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}) -> {}",
            self.inputs.iter().map(ToString::to_string).join(","),
            self.output
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Examples {
    positive_examples: Vec<TestCase>,
    negative_examples: Vec<TestCase>,
}

/// helper function
fn filter_behavior<T: TypeSystemBounds, P: Fn(&Constant) -> bool>(
    iter: Vec<TestCase>,
    cond: &LinearProgram<T>,
    predicate: P,
) -> Vec<TestCase> {
    iter.into_iter()
        .filter(|t: &TestCase| {
            let e = t.into();
            if let Ok(res) = cond.interpret(&e) {
                assert!(matches!(res, Constant::Bool(_)));
                predicate(&res)
            } else {
                info!("Had an invalid program while filtering behaviour: {cond}");
                false
            }
        })
        .collect::<Vec<TestCase>>()
}

/// helper function
fn filter_behavior_p<T: TypeSystemBounds, P: Fn(&Constant) -> bool>(
    iter: Vec<TestCase>,
    cond: &Program<T>,
    predicate: &P,
) -> Vec<TestCase> {
    iter.into_iter()
        .filter(|t: &TestCase| {
            let e = t.into();
            if let Ok(res) = cond.interpret(&e, cond) {
                assert!(matches!(res, Constant::Bool(_)));
                predicate(&res)
            } else {
                info!("Had an invalid program while filtering behaviour: {cond}");
                false
            }
        })
        .collect::<Vec<TestCase>>()
}

impl Examples {
    pub fn new(positive_examples: Vec<TestCase>, negative_examples: Vec<TestCase>) -> Self {
        Self {
            positive_examples,
            negative_examples,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.positive_examples.is_empty() && self.negative_examples.is_empty()
    }

    pub fn extend(&mut self, other: Examples) {
        self.positive_examples.extend(other.positive_examples);
        self.negative_examples.extend(other.negative_examples);
    }

    pub fn get_positive_examples(&self) -> &[TestCase] {
        &self.positive_examples
    }

    pub fn get_negative_examples(&self) -> &[TestCase] {
        &self.negative_examples
    }

    pub fn get_all_examples(&self) -> Vec<TestCase> {
        let mut res = self.positive_examples.clone();
        res.extend(self.negative_examples.clone());
        res
    }

    pub fn filter_behavior<T: TypeSystemBounds, P: Fn(&Constant) -> bool>(
        &self,
        cond: &LinearProgram<T>,
        predicate: P,
    ) -> Examples {
        let Examples {
            positive_examples,
            negative_examples,
        } = self;
        Examples::new(
            filter_behavior(positive_examples.clone(), cond, &predicate),
            filter_behavior(negative_examples.clone(), cond, &predicate),
        )
    }

    pub fn filter_behavior_p<T: TypeSystemBounds, P: Fn(&Constant) -> bool>(
        &self,
        cond: &Program<T>,
        predicate: &P,
    ) -> Examples {
        let Examples {
            positive_examples,
            negative_examples,
        } = self;
        Examples::new(
            filter_behavior_p(positive_examples.clone(), cond, predicate),
            filter_behavior_p(negative_examples.clone(), cond, predicate),
        )
    }

    /// Provide a list of examples for each argument of the operation.
    /// TODO, this may be a source of confusion... will have to wait and see
    pub fn witness_examples<T: TypeSystemBounds>(
        &self,
        o: &Operation<T>,
        inverse_map: &InverseMap<T>,
    ) -> Option<Vec<Vec<Examples>>> {
        (0..o.sig.input.len())
            .map(|idx| inverse_map.inverse_app(o, self, idx))
            .collect()
    }

    pub fn propogate_operation_examples<T: TypeSystemBounds>(
        &self,
        o: &Operation<T>,
        inverse_map: &InverseMap<T>,
    ) -> Option<Vec<Vec<Examples>>> {
        (0..o.sig.input.len())
            .map(|idx| inverse_map.inverse_app(o, self, idx))
            .collect::<Option<_>>()
            .map(|i: Vec<_>| i.into_iter().multi_cartesian_product().collect())
    }

    /// Helper for getting a set of examples for the arguments to a recursive function.
    /// Does not translate over any negative examples
    pub fn rec_compute_example_args(&self, num_args: usize) -> Vec<Examples> {
        (0..num_args)
            .map(|idx| {
                Examples::new(
                    self.positive_examples
                        .clone()
                        .into_iter()
                        .map(|mut t| {
                            t.output = t.inputs[idx].clone();
                            t
                        })
                        .collect_vec(),
                    Vec::new(),
                )
            })
            .collect()
    }

    // New examples for the inter recursive case
    pub fn rec_new_examples(&self, other: &Examples) -> Examples {
        let mut new_examples = Vec::new();
        for t in self.positive_examples.clone().into_iter() {
            if !other.positive_examples.contains(&t) {
                new_examples.push(t);
            }
        }
        Examples::new(new_examples, Vec::new())
    }

    pub fn combine(&self, other: &Examples) -> Examples {
        let mut combined = self.clone();
        combined.extend(other.clone());
        combined
    }

    pub fn is_consistent_with<F: Fn(&TestCase) -> bool>(&self, f: F) -> bool {
        self.positive_examples.iter().all(&f) && self.negative_examples.iter().all(|t| !f(t))
    }
}

impl Display for Examples {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{pos: [{}], neg: [{}]}}",
            self.positive_examples
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.negative_examples
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Union {
    universe: Vec<Examples>,
}
