use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use log::info;

use crate::{
    language::{Constant, Examples},
    Fragment, FragmentCollection, Libraries, Operation, TestCase, TypeSystemBounds,
};

#[derive(Debug)]
pub struct InverseMap<T: TypeSystemBounds> {
    map: HashMap<Operation<T>, Vec<TestCase>>,
}

impl<T: TypeSystemBounds> InverseMap<T> {
    pub fn new(l: &Libraries<T>, frags: &FragmentCollection<T>) -> Self {
        let FragmentCollection { inner, .. } = frags;
        let type_map: HashMap<T, HashSet<Constant>> = inner
            .iter()
            .map(|Fragment { ty, behavior, .. }| {
                (ty, behavior.iter().map(|TestCase { output, .. }| output))
            })
            .fold(HashMap::new(), |mut acc, (t, os)| {
                let e = acc.entry(t.clone()).or_default();
                os.for_each(|o| {
                    e.insert(o.clone());
                });
                acc
            });

        let temp_set = HashSet::new();

        let map: HashMap<Operation<T>, Vec<TestCase>> = l
            .iter()
            .map(|o| {
                let args = o
                    .sig
                    .input
                    .iter()
                    .map(|i| type_map.get(i).unwrap_or(&temp_set).iter())
                    .multi_cartesian_product();

                let tests: Vec<_> = args
                    .filter_map(|a| {
                        let inputs = a.into_iter().cloned().collect();
                        let output = o.execute(&inputs).ok()?;
                        Some(TestCase { inputs, output })
                    })
                    .collect();
                (o.clone(), tests)
            })
            .collect();

        InverseMap { map }
    }

    /// Return a list of possible examples for a given index into the operation
    pub fn inverse_app(
        &self,
        o: &Operation<T>,
        hole: &Examples,
        idx: usize,
    ) -> Option<Vec<Examples>> {
        /* info!("Computing inverse app for {o}"); */
        // Get all the inverse semantics for the operation
        let inverse_semantics = self.map.get(o).unwrap();

        // Filter out the inverse semantics that don't match the given testcase in the example
        let t_iter = hole
            .get_positive_examples()
            .iter()
            .map(|TestCase { inputs, output }| {
                inverse_semantics
                    .iter()
                    .filter(|x| x.output == *output)
                    .map(|x| {
                        let new_inputs = inputs.clone();
                        let new_output = x.inputs.get(idx).unwrap().clone();
                        TestCase {
                            inputs: new_inputs,
                            output: new_output,
                        }
                    })
                    .collect_vec()
            });

        // If any of these didn't work out, then we don't have inverse semantics for one of the fuction arguments
        if t_iter.clone().any(|i| i.is_empty()) {
            /* info!("Inverse app is empty for {o}, {hole}"); */
            return None;
        }

        // Given a nested list of possible testcases for each part of the example, combine them all together into as many example holes as needed
        Some(
            t_iter
                .multi_cartesian_product()
                .map(|args| Examples::new(args, hole.get_negative_examples().to_vec()))
                .collect(),
        )
    }
}
