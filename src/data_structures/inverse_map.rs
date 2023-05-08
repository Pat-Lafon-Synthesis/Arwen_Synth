use std::collections::{HashMap, HashSet};

use itertools::Itertools;

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

        dbg!(&type_map);

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
                        dbg!(&a);
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

    pub fn inverse_app(&self, o: &Operation<T>, hole: &Examples, idx: usize) -> Vec<Examples> {
        let inverse_semantics = self.map.get(o).unwrap();

        hole.iter()
            .map(|TestCase { inputs, output }| {
                inverse_semantics
                    .iter()
                    .filter(|t| t.output == *output)
                    .map(|x| {
                        let new_inputs = inputs.clone();
                        let new_output = x.inputs.get(idx).unwrap().clone();
                        TestCase {
                            inputs: new_inputs,
                            output: new_output,
                        }
                    })
                    .collect_vec()
            })
            .filter(|i| i.is_empty())
            .multi_cartesian_product()
            .map(|args| args.into())
            .collect()
    }
}
