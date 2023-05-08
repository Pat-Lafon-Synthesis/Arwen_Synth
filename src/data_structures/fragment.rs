use std::{collections::HashMap, fmt::Display, num::NonZeroU8};

use itertools::Itertools;

use crate::{
    language::Examples, Libraries, Operation, Program, ProgramNode, Signature, TestCase,
    TypeSystemBounds, Variable,
};

#[derive(Debug, Clone, Eq)]
pub struct Fragment<T: TypeSystemBounds> {
    size: NonZeroU8,
    pub ty: T,
    pub fragment: Program<T>,
    pub behavior: Vec<TestCase>,
}

impl<T: TypeSystemBounds> PartialEq for Fragment<T> {
    fn eq(&self, other: &Self) -> bool {
        self.behavior == other.behavior
    }
}

impl<T: TypeSystemBounds> PartialOrd for Fragment<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.size.partial_cmp(&other.size) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.behavior.partial_cmp(&other.behavior)
    }
}

impl<T: TypeSystemBounds> Ord for Fragment<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<T: TypeSystemBounds> Display for Fragment<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}\n\t{}\n",
            self.fragment,
            self.behavior.iter().map(ToString::to_string).join("\n\t")
        )
    }
}

#[derive(Debug)]
pub struct FragmentCollection<T: TypeSystemBounds> {
    size: NonZeroU8,
    pub inner: Vec<Fragment<T>>,
}

impl<T: TypeSystemBounds> Display for FragmentCollection<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "size = {}\nfargments:\n{}",
            self.size,
            self.inner.iter().map(ToString::to_string).join("\n")
        )
    }
}

impl<T: TypeSystemBounds> FragmentCollection<T> {
    pub fn new(
        vars: Vec<Variable<T>>,
        libraries: &Libraries<T>,
        testcases: Examples,
    ) -> FragmentCollection<T> {
        let size = NonZeroU8::new(1).unwrap();

        FragmentCollection {
            size,
            inner: vars
                .into_iter()
                .map(|ref v @ Variable { ref ty, .. }| {
                    let fragment = Program {
                        node: ProgramNode::Variable(v.clone(), ty.clone()),
                        args: Vec::new(),
                    };

                    let behavior = fragment.get_behavior(&testcases);

                    Fragment {
                        size,
                        ty: ty.clone(),
                        fragment,
                        behavior,
                    }
                })
                .chain(libraries.iter().filter_map(
                    |o @ Operation {
                         sig: Signature { input, output },
                         ..
                     }| {
                        if !input.is_empty() {
                            None
                        } else {
                            let fragment = Program {
                                node: ProgramNode::Operation(o.clone()),
                                args: Vec::new(),
                            };

                            let behavior = fragment.get_behavior(&testcases);

                            Some(Fragment {
                                size,
                                ty: output.clone(),
                                fragment,
                                behavior,
                            })
                        }
                    },
                ))
                .collect(),
        }
    }

    fn has_behavior(&self, behavior: &Vec<TestCase>) -> bool {
        self.inner.iter().any(|f| &f.behavior == behavior)
    }

    pub fn get_size(&self) -> NonZeroU8 {
        self.size
    }

    pub fn get_all_sorted(&self, ty: &T) -> Vec<&Fragment<T>> {
        self.inner
            .iter()
            .filter(|f| &f.ty == ty)
            .sorted_by_key(|f| f.size)
            .collect()
    }

    pub fn increment(&mut self, l: &Libraries<T>, testcases: &[TestCase]) {
        // grab all components for each type
        let component_map: HashMap<T, Vec<Fragment<T>>> =
            self.inner.iter().fold(HashMap::new(), |mut acc, f| {
                acc.entry(f.ty.clone())
                    .and_modify(|e: &mut Vec<Fragment<T>>| e.push(f.clone()))
                    .or_insert(vec![f.clone()]);
                acc
            });

        // grab all components the current size
        let current_size_component_map: HashMap<T, Vec<Fragment<T>>> = component_map
            .iter()
            .map(|(k, vs)| {
                (
                    k.clone(),
                    vs.iter().filter(|v| v.size == self.size).cloned().collect(),
                )
            })
            .collect();

        let new_size = self.size.checked_add(1).unwrap();
        // Create a bunch of new fragments that are strictly one size larger
        let mut new_fragments = l
            .iter()
            .flat_map(|o| -> Vec<Fragment<T>> {
                (0..o.sig.input.len())
                    .flat_map(|idx| -> Vec<Vec<Fragment<T>>> {
                        o.sig
                            .input
                            .iter()
                            .enumerate()
                            .map(|(i, ty)| {
                                if i == idx {
                                    current_size_component_map
                                        .get(ty)
                                        .cloned()
                                        .unwrap_or_default()
                                        .into_iter()
                                } else {
                                    component_map
                                        .get(ty)
                                        .cloned()
                                        .unwrap_or_default()
                                        .into_iter()
                                }
                            })
                            .multi_cartesian_product()
                            .collect()
                    })
                    .map(|args| {
                        let fragment = Program {
                            node: ProgramNode::Operation(o.clone()),
                            args: args.into_iter().map(|f| f.fragment).collect(),
                        };
                        let behavior = fragment.get_behavior(testcases);
                        Fragment {
                            size: new_size,
                            ty: o.sig.output.clone(),
                            fragment,
                            behavior,
                        }
                    })
                    .filter(|f| !self.has_behavior(&f.behavior))
                    .collect()
            })
            .sorted()
            .dedup()
            .collect();

        // add these fragments to the collection
        self.inner.append(&mut new_fragments);

        // increment Fragment Collection size
        self.size = self.size.checked_add(1).unwrap();
    }

    pub fn find_valid_traces(&self, exs: &Examples) -> Vec<&Fragment<T>> {
        self.inner
            .iter()
            .filter(|Fragment { behavior, .. }| behavior.iter().any(|t| exs.contains(t)))
            .collect()
    }
}
