#![feature(iterator_try_collect)]
#![feature(unboxed_closures)]
#![feature(fn_traits)]
#![feature(slice_group_by)]
#![feature(is_sorted)]
#![feature(exact_size_is_empty)]
#![feature(let_chains)]
#![feature(trait_alias)]

pub mod language;
pub mod parser_interface;
pub mod types;

use itertools::Itertools;
use log::{info, warn};
use std::cmp::{Ordering, Reverse};
use std::collections::BinaryHeap;
use std::hash::Hash;
use std::iter::once;
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    num::NonZeroU64,
};

use language::*;
use types::*;

use ecta_rs::{ECTANode, Edge, Node, ECTA};

const if_depth: usize = 1;

#[derive(Debug)]
pub struct InverseMap<T: TypeSystemBounds> {
    pub map: HashMap<Operation<T>, Vec<TestCase>>,
}

impl<T: TypeSystemBounds> InverseMap<T> {
    pub fn new(l: &Libraries<T>, FragmentCollection { inner, .. }: &FragmentCollection<T>) -> Self {
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

    pub fn inverse_app(&self, o: &Operation<T>, hole: &Vec<TestCase>, idx: usize) -> Vec<TestCase> {
        let mut ret = Vec::new();

        let inverse_semantics = self.map.get(o).unwrap();

        dbg!(&inverse_semantics);
        dbg!(&hole);
        dbg!(idx);

        for TestCase { inputs, output } in hole {
            let new_inputs = inputs.clone();

            if let Some(x) = inverse_semantics.iter().find(|t| t.output == *output) {
                let new_output = x.inputs.get(idx).unwrap().clone();

                ret.push(TestCase {
                    inputs: new_inputs,
                    output: new_output,
                });
            }
        }
        ret
    }
}

type Libraries<T> = Vec<Operation<T>>;

#[derive(Debug, Clone, Eq, Ord)]
pub struct Fragment<T: TypeSystemBounds> {
    size: NonZeroU64,
    ty: T,
    fragment: Program<T>,
    behavior: Vec<TestCase>,
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
    size: NonZeroU64,
    inner: Vec<Fragment<T>>,
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
    fn new(
        vars: Vec<Variable<T>>,
        libraries: &Libraries<T>,
        testcases: Vec<TestCase>,
    ) -> FragmentCollection<T> {
        let size = NonZeroU64::new(1).unwrap();

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

    fn increment(&mut self, l: &Libraries<T>, testcases: &Vec<TestCase>) {
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
            .map(|o| -> Vec<Fragment<T>> {
                (0..o.sig.input.len())
                    .map(|idx| -> Vec<Vec<Fragment<T>>> {
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
                            ty: o.sig.output.clone(),
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

fn transpose<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>> {
    assert!(!v.is_empty());
    let len = v[0].len();
    let mut iters: Vec<_> = v.into_iter().map(|n| n.into_iter()).collect();
    (0..len)
        .map(|_| {
            iters
                .iter_mut()
                .map(|n| n.next().unwrap())
                .collect::<Vec<T>>()
        })
        .collect()
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SynthEctaEdge {
    P(LinearProgramNode<BaseType>),
    T(BaseType),
}

impl<'a> TryFrom<&'a SynthEctaEdge> for &'a LinearProgramNode<BaseType> {
    type Error = ();

    fn try_from(value: &'a SynthEctaEdge) -> Result<Self, Self::Error> {
        match value {
            SynthEctaEdge::P(p) => Ok(p),
            _ => Err(()),
        }
    }
}

impl Display for SynthEctaEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SynthEctaEdge::P(p) => write!(f, "{}", p),
            SynthEctaEdge::T(t) => write!(f, "{}", t),
        }
    }
}

#[derive(Clone, Copy)]
struct SynthesizerState<'a> {
    pub ecta: &'a ECTA<SynthEctaEdge, ()>,
    pub inverse_map: &'a InverseMap<BaseType>,
    pub bool_fragments: &'a Vec<&'a Fragment<BaseType>>,
}

impl<'a> SynthesizerState<'a> {
    pub fn new(
        ecta: &'a ECTA<SynthEctaEdge, ()>,
        inverse_map: &'a InverseMap<BaseType>,
        bool_fragments: &'a Vec<&'a Fragment<BaseType>>,
    ) -> Self {
        Self {
            ecta,
            inverse_map,
            bool_fragments,
        }
    }
}

fn create_ecta_from_traces(
    ecta: &mut ECTA<SynthEctaEdge, ()>,
    frags: &[&Program<BaseType>],
) -> ECTANode {
    info!("Starting ECTA creation from traces...");

    if frags.is_empty() {
        warn!("create_ecta_from_traces called with empty fragment list")
    }

    frags.iter().for_each(|p| {
        info!("program in fragments = {}", p);
    });

    let edge_builder = frags
        .group_by(|p1, p2| p1.node == p2.node)
        .map(|g| {
            let prog_edge = SynthEctaEdge::P(g[0].node.clone().try_into().unwrap());
            let ty_edge = SynthEctaEdge::T(g[0].into());

            let type_node =
                ecta.add_node(Node::new(), vec![(ty_edge, None, vec![ecta.empty_node])]);

            let mut node_collector = vec![type_node];
            if let ProgramNode::Operation(_) = g[0].node {
                let x = g
                    .into_iter()
                    .map(|Program { node, args }| match node {
                        ProgramNode::Constant(..) | ProgramNode::Variable(..) => unreachable!(),
                        ProgramNode::Operation(_) => args.clone(),
                        ProgramNode::If => unreachable!(),
                    })
                    .collect::<Vec<_>>();
                let traces = transpose(x);
                let traces = traces
                    .iter()
                    .map(|a| a.iter().collect::<Vec<_>>())
                    .collect::<Vec<_>>();
                traces.into_iter().for_each(|trace| {
                    let inner_node = create_ecta_from_traces(ecta, &trace);
                    node_collector.push(inner_node);
                });
            }

            (prog_edge, None, node_collector)
        })
        .collect();

    let program_node = ecta.add_node(Node::new(), edge_builder);

    info!("Done with ECTA creation from traces...");

    program_node
}
/*
type SynthIterInner = std::vec::IntoIter<(
    LinearProgramNode<BaseType>,
    Vec<Edge<LinearProgramNode<BaseType>, ()>>,
)>;

#[derive(Clone, Copy)]
struct SynthesizerState<'a> {
    pub ecta: &'a ECTA<SynthEctaEdge, ()>,
    pub inverse_map: &'a InverseMap<BaseType>,
    pub bool_fragments: &'a Vec<&'a Fragment<BaseType>>,
    pub if_depth: usize,
    pub recursion_allowed: bool,
}

impl<'a> SynthesizerState<'a> {
    pub fn new(
        ecta: &'a ECTA<SynthEctaEdge, ()>,
        inverse_map: &'a InverseMap<BaseType>,
        bool_fragments: &'a Vec<&'a Fragment<BaseType>>,
    ) -> Self {
        Self {
            ecta,
            inverse_map,
            bool_fragments,
            if_depth: 0,
            recursion_allowed: false,
        }
    }
}

#[derive(Clone)]
struct SynthIterator<'a> {
    state: SynthesizerState<'a>,
    components: Vec<Sketch<BaseType>>,
    holes: Vec<TestCase>,
    target_type: BaseType,
}

impl<'a> SynthIterator<'a> {
    pub fn new(state: SynthesizerState<'a>, holes: Vec<TestCase>, target_type: BaseType) -> Self {
        Self {
            state,
            components: Vec::new(),
            holes,
            target_type,
        }
    }

    pub fn empty(state: SynthesizerState<'a>, holes: Vec<TestCase>, target_type: BaseType) -> Self {
        Self {
            state,
            components: Vec::new(),
            holes,
            target_type,
        }
    }
}

impl<'a> Iterator for SynthIterator<'a> {
    type Item = Program<BaseType>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.queue.pop() && p.passes_all_test_cases(&self.holes) && p.get_type() == self.target_type {
            Some(p)
        } else if self.components.is_empty() {
            None
        } else {
            assert!(self.queue.pop().is_none());
            let (p_node, mut edge_group) = self.components.next().unwrap();

            self.queue = match p_node {
                LinearProgramNode::Constant(_) => {
                    Box::new(Some(Program {
                        node: p_node.into(),
                        args: Vec::new(),
                    }).into_iter())
                }
                LinearProgramNode::Variable(..) => {
                    Box::new(Some(Program {
                        node: p_node.clone().into(),
                        args: Vec::new(),
                    }).into_iter())
                }
                LinearProgramNode::Operation(ref o) => {
                    info!("Operation = {}", o);

                    dbg!(&edge_group);
                    edge_group.remove(0);

                    assert!(o.sig.input.len() == edge_group.len());
                    assert!(edge_group.is_sorted_by_key(|e| e.nodeidx));

                    let mut args = Vec::new();

                    for e in edge_group {
                        let hole = self.state.inverse_map.inverse_app(
                            &o,
                            &self.holes,
                            (e.edge_num - 1) as usize,
                        );

                        let p_sub = deduce(
                            self.state,
                            e.nodeidx,
                            hole,
                            o.sig.input[(e.edge_num - 1) as usize],
                        );

                        args.push(p_sub);
                    }

                    let p_node : ProgramNode<_> = p_node.into();

                    let sets_of_things = repeat(p_node).zip(args.into_iter().multi_cartesian_product());

                    let x = sets_of_things.map(Program::new);

                    Box::new(
                        x
                    )
                }
            };

            if self.state.if_depth < if_depth {
                todo!()
            }

            self.next()
        }
    }
}
 */
/* impl<'a> Iterator for SynthIterator<'a> {
    type Item = Program<BaseType>;

    fn next(&mut self) -> Option<Self::Item> {
        let p = if let Some((p_node, mut edge_group)) = self.components.next() {
            if self.state.if_depth < if_depth {
                // If candidate
                self.state.bool_fragments.iter().for_each(|b| {
                    self.if_candidates
                        .push((b, p_node.clone(), edge_group.clone()))
                });

                // Set up the proper order for constructing if candidates
                if self.components.is_empty() {
                    self.if_candidates.reverse();
                }
            };
            match p_node {
                LinearProgramNode::Constant(_) => {
                    Some(Program {
                        node: p_node.into(),
                        args: Vec::new(),
                    })
                }
                LinearProgramNode::Variable(..) => {
                    Some(Program {
                        node: p_node.clone().into(),
                        args: Vec::new(),
                    })
                }
                LinearProgramNode::Operation(ref o) => {
                    info!("Operation = {}", o);

                    dbg!(&edge_group);
                    edge_group.remove(0);

                    assert!(o.sig.input.len() == edge_group.len());
                    assert!(edge_group.is_sorted_by_key(|e| e.nodeidx));

                    let mut args = Vec::new();

                    for e in edge_group {
                        let hole = self.state.inverse_map.inverse_app(
                            &o,
                            self.holes,
                            (e.edge_num - 1) as usize,
                        );

                        let p_sub = deduce(
                            self.state,
                            e.nodeidx,
                            &hole,
                            o.sig.input[(e.edge_num - 1) as usize],
                        )
                        .next()?;

                        args.push(p_sub);
                    }
                    Some(Program {
                        node: p_node.into(),
                        args,
                    })
                }
            }
        } else {
            if let Some((cond_p, p_node, edge_group)) = self.if_candidates.pop() {
                assert!(self.state.if_depth < if_depth);

                // we want some kind of condition here
                // prioritize conditions that split test cases?
                let mut args = Vec::new();

                let (true_holes, false_holes): (Vec<_>, Vec<_>) =
                    self.holes.iter().partition(|t| {
                        match cond_p
                            .behavior
                            .iter()
                            .find(|inp| inp.inputs == t.inputs)
                            .unwrap()
                            .output
                        {
                            Constant::Bool(b) => b,
                            Constant::Int(_) | Constant::IntList(_) | Constant::IntTree(_) => {
                                unreachable!()
                            }
                        }
                    });

                args.push(cond_p.fragment.clone());


                Some(Program {
                    node: ProgramNode::If,
                    args,
                })
            } else {
                return None;
            }
        }
    }
} */

#[derive(PartialEq, Eq)]
struct HoleMetaData {
    path: Vec<u8>,
    nodeid: ECTANode,
    examples: Vec<TestCase>,
    typ: BaseType,
    if_depth: usize,
    recursion_allowed: bool,
}

#[derive(PartialEq, Eq)]
struct SketchWithData {
    sketch: Sketch<BaseType>,
    holes: Vec<HoleMetaData>,
}

impl PartialOrd for SketchWithData {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.sketch.partial_cmp(&other.sketch)
    }
}

impl Ord for SketchWithData {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

fn sketch_constructor<'a>(
    state: &'a SynthesizerState<'a>,
    sketch: Sketch<BaseType>,
    path: std::slice::Iter<'a, u8>,
) -> impl Fn(SketchWithData) -> SketchWithData + 'a {
    move |x| -> SketchWithData {
        let path = path.clone();
        let sketch = sketch.clone();
        fn helper<'a>(
            state: &'a SynthesizerState<'a>,
            x: SketchWithData,
            mut path: std::slice::Iter<'a, u8>,
            sketch: Sketch<BaseType>,
        ) -> SketchWithData {
            if path.is_empty() {
                x
            } else {
                let i = *path.next().unwrap();
                match sketch {
                    Sketch::Hole(_) | Sketch::Constant(_) | Sketch::Variable(..) => panic!(),
                    Sketch::Operation(o, mut args) => {
                        let SketchWithData { sketch, holes } =
                            helper(state, x, path, args[i as usize].clone());
                        args[i as usize] = sketch;

                        let holes = holes
                            .into_iter()
                            .map(|h| {
                                let examples =
                                    state.inverse_map.inverse_app(&o, &h.examples, i as usize);
                                HoleMetaData {
                                    path: once(i).chain(h.path).collect(),
                                    examples,
                                    nodeid: h.nodeid,
                                    typ: h.typ,
                                    if_depth,
                                    recursion_allowed: h.recursion_allowed,
                                }
                            })
                            .collect();

                        SketchWithData {
                            sketch: Sketch::Operation(o, args),
                            holes,
                        }
                    }
                    Sketch::If(..) => todo!(),
                }
            }
        }
        helper(state, x, path, sketch)
    }
}

fn get_edge_candidates<'a>(
    state: &SynthesizerState<'a>,
    holedata: &HoleMetaData,
) -> Vec<SketchWithData> {
    if holedata.nodeid == state.ecta.empty_node {
        info!("The empty node has no candidates");

        return Vec::new();
    }

    let edges = state.ecta.get_edges(holedata.nodeid).filter_map(|e| {
        if matches!(e.data, SynthEctaEdge::T(_)) {
            None
        } else {
            Some(e.clone().map(|s| match s {
                SynthEctaEdge::P(p) => p,
                _ => unreachable!(),
            }))
        }
    });

    if edges.clone().next().is_none() {
        info!("No edge candidates");
        return Vec::new();
    }

    let mut iterable: Vec<(
        LinearProgramNode<BaseType>,
        Vec<Edge<LinearProgramNode<BaseType>, ()>>,
    )> = Vec::new();

    edges
        .sorted_by(|a, b| a.data.cmp(&b.data))
        .group_by(|edge| edge.data.clone())
        .into_iter()
        .for_each(|(k, v)| {
            iterable.push((
                k,
                v.into_iter()
                    .sorted_by(|p1, p2| p1.edge_num.cmp(&p2.edge_num))
                    .collect(),
            ))
        });

    iterable
        .into_iter()
        .map(|(p_node, edges)| match p_node {
            LinearProgramNode::Constant(c) => SketchWithData {
                sketch: Sketch::Constant(c),
                holes: Vec::new(),
            },
            LinearProgramNode::Variable(v, t) => SketchWithData {
                sketch: Sketch::Variable(v, t),
                holes: Vec::new(),
            },
            LinearProgramNode::Operation(o) => {
                let args = o.sig.input.iter().map(|t| Sketch::Hole(*t)).collect();
                let holes = o
                    .sig
                    .input
                    .iter()
                    .zip(edges.iter())
                    .map(|(t, e)| HoleMetaData {
                        path: vec![e.edge_num],
                        examples: todo!(),
                        nodeid: e.nodeidx,
                        typ: *t,
                        if_depth: holedata.if_depth,
                        recursion_allowed: holedata.recursion_allowed,
                    })
                    .collect();
                SketchWithData {
                    sketch: Sketch::Operation(o, args),
                    holes,
                }
            }
        })
        .collect()
}

fn fill_sketch_hole<'a>(
    state: &SynthesizerState<'a>,
    mut sketch: SketchWithData,
) -> Vec<SketchWithData> {
    // What do you need to fill a sketch?
    // Where is the hole?
    // What can I fill it with?
    // Sketch has a spine to the location of the hole
    // Sketch has a node in the ecta

    let holedata = sketch.holes.pop().unwrap();
    // walk to the hole,
    // then construct new ones with the hole filled(possibly with new holes)
    let f = sketch_constructor(state, sketch.sketch, holedata.path.iter());

    let candidates = get_edge_candidates(state, &holedata);

    let sketches = candidates.into_iter().map(f).collect();

    /*
        state.if_depth;
        state.recursion_allowed;

        // If recursive call, check extra consistency
        todo!();
    */
    sketches
}

fn complete_sketch(sketch: &SketchWithData) -> bool {
    sketch.holes.is_empty()
}

struct MinHeap<T: Ord>(BinaryHeap<Reverse<T>>);

impl<T: Ord> MinHeap<T> {
    fn new() -> Self {
        MinHeap(BinaryHeap::new())
    }
    fn push(&mut self, item: T) {
        self.0.push(Reverse(item))
    }

    fn pop(&mut self) -> Option<T> {
        self.0.pop().map(|Reverse(item)| item)
    }
}

fn deduce2<'a>(
    state: SynthesizerState<'a>,
    node: ECTANode,
    hole: Vec<TestCase>,
    target_type: BaseType,
) -> Option<Program<BaseType>> {
    info!("start deduction");
    if node == state.ecta.empty_node {
        warn!("Empty node in deduce");
        panic!();
    }

    let initial = SketchWithData {
        sketch: Sketch::Hole(target_type),
        holes: vec![HoleMetaData {
            path: Vec::new(),
            examples: hole,
            nodeid: node,
            typ: target_type,
            if_depth: 0,
            recursion_allowed: false,
        }],
    };

    let mut queue = MinHeap::new();
    queue.push(initial);

    while let Some(sketch) = queue.pop() {
        for s in fill_sketch_hole(&state, sketch) {
            if complete_sketch(&s) {
                return s.sketch.try_into().ok();
            } else {
                queue.push(s);
            }
        }
    }

    None
}

/* fn deduce<'a>(
    state: SynthesizerState<'a>,
    node: ECTANode,
    hole: Vec<TestCase>,
    target_type: BaseType,
) -> SynthIterator<'a> {
    if node == state.ecta.empty_node {
        info!("Empty node in deduce");

        return SynthIterator::empty(state, hole, target_type);
    }

    let edges = state.ecta.get_edges(node).filter_map(|e| {
        if matches!(e.data, SynthEctaEdge::T(_)) {
            None
        } else {
            Some(e.clone().map(|s| match s {
                SynthEctaEdge::P(p) => p,
                _ => unreachable!(),
            }))
        }
    });

    if edges.clone().next().is_none() {
        info!("No edges to deduce");
        return SynthIterator::empty(state, hole, target_type);
    }

    let mut iterable = Vec::new();

    edges
        .sorted_by(|a, b| a.data.cmp(&b.data))
        .group_by(|edge| edge.data.clone())
        .into_iter()
        .for_each(|(k, v)| {
            iterable.push((
                k,
                v.into_iter()
                    .sorted_by(|p1, p2| p1.edge_num.cmp(&p2.edge_num))
                    .collect(),
            ))
        });

    info!("Ordering groups by some kind of cost");

    SynthIterator::new(state, iterable.into_iter(), hole, target_type)
}
 */
fn top_down_prop(
    hole: Vec<TestCase>,
    traces: Vec<&Fragment<BaseType>>,
    inverse_map: &InverseMap<BaseType>,
    fragment_collection: &FragmentCollection<BaseType>,
    target_type: BaseType,
) -> Option<Program<BaseType>> {
    info!("Starting top down propagation...");
    // Bail out early if there are no traces
    if traces.is_empty() {
        info!("No traces to propagate from");
        return None;
    }

    let mut ecta = ECTA::new();
    let top_node = create_ecta_from_traces(
        &mut ecta,
        &traces
            .iter()
            .map(|Fragment { fragment, .. }| fragment)
            .collect::<Vec<_>>(),
    );

    info!("Ecta = {}", ecta.get_dot());

    // Used in generating if conditions
    let bool_fragments = fragment_collection
        .inner
        .iter()
        .filter(|f| f.ty == BaseType::Bool)
        .sorted_by_key(|f| f.size)
        .collect();

    let synthesis_state = SynthesizerState::new(&ecta, inverse_map, &bool_fragments);

    let prog_iter = deduce2(synthesis_state, top_node, hole.clone(), target_type);

    prog_iter.filter(|p| p.passes_all_test_cases(&hole))
}

pub fn synthesis(
    sig: Signature<BaseType>,
    l: &Libraries<BaseType>,
    tests: &Vec<TestCase>,
    mut size: u8,
) -> Option<Program<BaseType>> {
    use std::io::Write;
    env_logger::builder()
        .format(|buf, record| {
            writeln!(
                buf,
                "{}:{} [{}] - {}",
                record.file().unwrap_or("unknown"),
                record.line().unwrap_or(0),
                record.level(),
                record.args()
            )
        })
        .try_init()
        .unwrap();
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

    info!("Starting synthesis...");
    info!("Incoming tests = {:#?}", tests);

    loop {
        info!("Sample the libraries");

        let inverse_map = InverseMap::new(l, &frags);

        info!("Creating traces");
        let traces: Vec<&Fragment<BaseType>> = frags
            .inner
            .iter()
            .filter(|Fragment { behavior, .. }| behavior.iter().any(|t| tests.contains(t)))
            .collect();

        info!("Printing traces of up to size {}", frags.size);
        traces.iter().for_each(|t| info!("trace = {t}"));

        let complete_traces: Vec<_> = traces
            .iter()
            .filter(|Fragment { behavior, .. }| tests.iter().all(|t| behavior.contains(t)))
            .collect();
        if !complete_traces.is_empty() {
            return Some(complete_traces.first().unwrap().fragment.clone());
        }

        // Synthesize candidates topdown propagation (with holes?)
        // work top down, trying to follow the traces?
        if let Some(p) = top_down_prop(tests.clone(), traces, &inverse_map, &frags, sig.output) {
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
