use std::{
    fmt::{Debug, Display},
    ops::{Deref, DerefMut},
};

use itertools::Itertools;
use log::info;

use crate::{data_structures::InverseMap, types::TypeSystemBounds};

use super::{Constant, LinearProgram, Operation, Program};

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

#[derive(Clone, PartialEq, Eq)]
pub struct Examples(Vec<TestCase>);

impl Deref for Examples {
    type Target = Vec<TestCase>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Examples {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Debug for Examples {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl From<Vec<TestCase>> for Examples {
    fn from(value: Vec<TestCase>) -> Self {
        Examples(value)
    }
}

impl IntoIterator for Examples {
    type Item = TestCase;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Examples {
    pub fn new(tests: Vec<TestCase>) -> Self {
        Examples(tests)
    }

    pub fn filter_behavior<T: TypeSystemBounds, P: Fn(&Constant) -> bool>(
        &self,
        cond: &LinearProgram<T>,
        predicate: P,
    ) -> Examples {
        self.clone()
            .into_iter()
            .filter(|t| {
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
            .into()
    }

    pub fn filter_behavior_p<T: TypeSystemBounds, P: Fn(&Constant) -> bool>(
        &self,
        cond: &Program<T>,
        predicate: P,
    ) -> Examples {
        self.clone()
            .into_iter()
            .filter(|t| {
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
            .into()
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

    /// Helper for getting a set of examples for the arguments to a recursive function.
    pub fn rec_compute_example_args(&self, num_args: usize) -> Vec<Examples> {
        (0..num_args)
            .map(|idx| {
                self.clone()
                    .into_iter()
                    .map(|mut t| {
                        t.output = t.inputs[idx].clone();
                        t
                    })
                    .collect_vec()
                    .into()
            })
            .collect()
    }

    // New examples for the inter recursive case
    pub fn rec_new_examples(&self, other: &Examples) -> Examples {
        let mut new_examples = Vec::new();
        for t in self.clone().into_iter() {
            if !other.contains(&t) {
                new_examples.push(t);
            }
        }
        new_examples.into()
    }

    pub fn combine(&self, other: &Examples) -> Examples {
        let mut combined = self.clone();
        combined.extend(other.clone());
        combined
    }
}

impl Display for Examples {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}]",
            self.iter()
                .map(|t| t.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}
