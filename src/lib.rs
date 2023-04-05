#![feature(iterator_try_collect)]
#![feature(unboxed_closures)]
#![feature(fn_traits)]
#![feature(slice_group_by)]

pub mod language;
pub mod parser_interface;
pub mod types;

use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    num::NonZeroU64,
};

use language::*;
use types::*;

use ecta_rs::{ECTANode, Node, ECTA};

pub struct InverseMap {
    pub map: HashMap<Operation, Vec<TestCase>>,
}

impl InverseMap {
    pub fn new(l: &Libraries, FragmentCollection { inner, .. }: &FragmentCollection) -> Self {
        let type_map: HashMap<BaseType, HashSet<Constant>> = inner
            .iter()
            .map(|Fragment { ty, behavior, .. }| {
                (ty, behavior.iter().map(|TestCase { output, .. }| output))
            })
            .fold(HashMap::new(), |mut acc, (t, os)| {
                let e = acc.entry(*t).or_default();
                os.for_each(|o| {
                    e.insert(o.clone());
                });
                acc
            });

        let temp_set = HashSet::new();

        let map: HashMap<Operation, Vec<TestCase>> = l
            .iter()
            .filter_map(|o| -> Option<_> {
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
                Some((o.clone(), tests))
            })
            .collect();

        InverseMap { map }
    }
}

type Libraries = Vec<Operation>;

#[derive(Debug, Clone, Eq, Ord)]
pub struct Fragment {
    size: NonZeroU64,
    ty: BaseType,
    fragment: Program,
    behavior: Vec<TestCase>,
}

impl PartialEq for Fragment {
    fn eq(&self, other: &Self) -> bool {
        self.behavior == other.behavior
    }
}

impl PartialOrd for Fragment {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.size.partial_cmp(&other.size) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.behavior.partial_cmp(&other.behavior)
    }
}

impl Display for Fragment {
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
pub struct FragmentCollection {
    size: NonZeroU64,
    inner: Vec<Fragment>,
}

impl Display for FragmentCollection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "size = {}\nfargments:\n{}",
            self.size,
            self.inner.iter().map(ToString::to_string).join("\n")
        )
    }
}

impl FragmentCollection {
    fn new(
        vars: Vec<Variable>,
        libraries: &Libraries,
        testcases: Vec<TestCase>,
    ) -> FragmentCollection {
        let size = NonZeroU64::new(1).unwrap();

        FragmentCollection {
            size,
            inner: vars
                .into_iter()
                .map(|ref v @ Variable { ref ty, .. }| {
                    let fragment = Program {
                        node: ProgramNode::Variable(v.clone(), ty.clone().into()),
                        args: Vec::new(),
                    };

                    let behavior = fragment.get_behavior(&testcases);

                    Fragment {
                        size,
                        ty: (ty.clone()).into(),
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
                                ty: *output,
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

    fn increment(&mut self, l: &Libraries, testcases: &Vec<TestCase>) {
        // grab all components for each type
        let component_map: HashMap<BaseType, Vec<Fragment>> =
            self.inner.iter().fold(HashMap::new(), |mut acc, f| {
                acc.entry(f.ty)
                    .and_modify(|e: &mut Vec<Fragment>| e.push(f.clone()))
                    .or_insert(vec![f.clone()]);
                acc
            });

        // grab all components the current size
        let current_size_component_map: HashMap<BaseType, Vec<Fragment>> = component_map
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
            .map(|o| -> Vec<Fragment> {
                (0..o.sig.input.len())
                    .map(|idx| -> Vec<Vec<Fragment>> {
                        o.sig
                            .input
                            .iter()
                            .enumerate()
                            .map(|(i, ty)| {
                                if i == idx {
                                    current_size_component_map
                                        .get(ty)
                                        .cloned()
                                        .unwrap_or_else(|| Vec::new())
                                        .into_iter()
                                } else {
                                    component_map
                                        .get(ty)
                                        .cloned()
                                        .unwrap_or_else(|| Vec::new())
                                        .into_iter()
                                }
                            })
                            .multi_cartesian_product()
                            .collect()
                    })
                    .flatten()
                    .map(|args| {
                        let fragment = Program {
                            node: ProgramNode::Operation(o.clone()),
                            args: args.into_iter().map(|f| f.fragment).collect(),
                        };
                        let behavior = fragment.get_behavior(&testcases);
                        Fragment {
                            size: new_size,
                            ty: o.sig.output,
                            fragment,
                            behavior,
                        }
                    })
                    .filter(|f| !self.has_behavior(&f.behavior))
                    .collect()
            })
            .flatten()
            .sorted()
            .dedup()
            .collect();

        // add these fragments to the collection
        self.inner.append(&mut new_fragments);

        // increment Fragment Collection size
        self.size = self.size.checked_add(1).unwrap();
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SynthEctaEdge {
    P(ProgramNode),
    T(BaseType),
}

fn create_ecta_from_traces(ecta: &mut ECTA<SynthEctaEdge, ()>, frags: &[&Program]) -> ECTANode {
    frags.group_by(|p1, p2| p1.node == p2.node).for_each(|g| {
        g.into_iter().map(|Program { node, args }| {
            let (edge, ty) = match node {
                ProgramNode::Constant(c) => {
                    (SynthEctaEdge::P(node.clone()), SynthEctaEdge::T(c.into()))
                }
                ProgramNode::Variable(..) => todo!(),
                ProgramNode::Operation(_) => todo!(),
                ProgramNode::If => todo!(),
            };
            let mut end_nodes =
                vec![ecta.add_node(Node::new(), vec![(ty, None, vec![ecta.empty_node])])];

            /* end_nodes.append(args.iter()) */
        });

        /* ecta.add_node(
            Node::new(),
            vec![(g[0].fragment.node.clone(), None, vec![])],
        );*/
        todo!();
    });
    todo!()
}

fn top_down_prop(
    hole: Vec<Constant>,
    traces: Vec<&Fragment>,
    inverse_map: &InverseMap,
    within_if: bool,
) -> Option<Program> {
    let mut ecta = ECTA::new();
    create_ecta_from_traces(
        &mut ecta,
        &traces
            .iter()
            .map(|Fragment { fragment, .. }| fragment)
            .collect::<Vec<_>>(),
    );
    // Convert traces into walkable format like an ecta
    // Then actually walk them
    // This provides the opportunity to add if conditionals
    // And to add recursion though here to then quickly rewalk until a new hole I guess? To see if your valid
    // We need a map for conditionals? For each if conditional, we want to have a way to separate/use it...

    /* let ops: Vec<_> = traces
    .iter()
    .filter_map(
        |Fragment {
             size,
             ty,
             fragment: Program { node, args },
             behavior,
         }| {
            if match node {
                ProgramNode::Constant(_) => hole
                    .iter()
                    .all(|c| behavior.iter().any(|TestCase { output, .. }| output == c)),
                ProgramNode::Variable(_) => hole
                    .iter()
                    .all(|c| behavior.iter().any(|TestCase { output, .. }| output == c)),
                ProgramNode::Operation(o) => {
                    dbg!(&o);
                    let behavior = inverse_map.map.get(o).unwrap();
                    hole.iter()
                        .all(|c| behavior.iter().any(|TestCase { output, .. }| output == c))
                }
                ProgramNode::If => unreachable!(),
            } {
                Some(node)
            } else {
                None
            }
        },
    )
    .sorted()
    .dedup()
    .collect(); */

    None
}

pub fn synthesis(
    sig: Signature<RefinementType>,
    l: &Libraries,
    tests: Vec<TestCase>,
    mut size: u8,
) -> Option<Program> {
    let variables = sig
        .input
        .iter()
        .enumerate()
        .map(|(i, ty)| Variable {
            name: format!("arg{i}"),
            ty: ty.clone(),
        })
        .collect();
    let mut frags = FragmentCollection::new(variables, l, tests.clone());

    while size > 1 {
        frags.increment(l, &tests);
        size -= 1;
    }
    //println!("{frags}");
    loop {
        // Sample the libraries
        let inverse_map = InverseMap::new(l, &frags);

        // Create Traces
        let traces: Vec<&Fragment> = frags
            .inner
            .iter()
            .filter(|Fragment { behavior, .. }| behavior.iter().any(|t| tests.contains(t)))
            .collect();

        println!("Printing traces of up to size {}", frags.size);
        traces.iter().for_each(|t| println!("{t}"));

        let complete_traces: Vec<_> = traces
            .iter()
            .filter(|Fragment { behavior, .. }| tests.iter().all(|t| behavior.contains(t)))
            .collect();
        if !complete_traces.is_empty() {
            return Some(complete_traces.first().unwrap().fragment.clone());
        }

        // Synthesize candidates topdown propagation (with holes?)
        // work top down, trying to follow the traces?
        if let Some(p) = top_down_prop(
            tests
                .iter()
                .map(|TestCase { output, .. }| output.clone())
                .collect(),
            traces,
            &inverse_map,
            false,
        ) {
            return Some(p);
        } else {
            frags.increment(l, &tests);
            if frags.size > NonZeroU64::new(10).unwrap() {
                eprintln!("We failed to synthesize anything in a bound of size 10");
                return None;
            }
        }
    }
}
