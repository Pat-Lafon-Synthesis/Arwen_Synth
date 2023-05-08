#![feature(iterator_try_collect)]
#![feature(unboxed_closures)]
#![feature(fn_traits)]
#![feature(slice_group_by)]
#![feature(is_sorted)]
#![feature(exact_size_is_empty)]
#![feature(let_chains)]
#![feature(trait_alias)]
#![feature(const_option)]
#![feature(impl_trait_in_assoc_type)]

pub mod data_structures;
pub mod language;
pub mod parser_interface;
pub mod types;

use log::{info, warn};
use std::fmt::Display;
use std::hash::Hash;
use std::num::NonZeroU8;

use data_structures::*;
use language::*;
use types::*;

use ecta_rs::{ECTANode, Edge, Node, ECTA};

const IF_DEPTH: usize = 1;
const MAX_FRAG_SIZE: NonZeroU8 = NonZeroU8::new(5).unwrap();

type Libraries<T> = Vec<Operation<T>>;

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
pub enum SynthEctaEdge<T: TypeSystemBounds> {
    P(LinearProgramNode<T>),
    T(T),
}

impl<'a, T: TypeSystemBounds> TryFrom<&'a SynthEctaEdge<T>> for &'a LinearProgramNode<T> {
    type Error = ();

    fn try_from(value: &'a SynthEctaEdge<T>) -> Result<Self, Self::Error> {
        match value {
            SynthEctaEdge::P(p) => Ok(p),
            _ => Err(()),
        }
    }
}

impl<T: TypeSystemBounds> Display for SynthEctaEdge<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SynthEctaEdge::P(p) => write!(f, "{}", p),
            SynthEctaEdge::T(t) => write!(f, "{}", t),
        }
    }
}

pub type SynthEcta<T> = ECTA<SynthEctaEdge<T>, ()>;
pub type SynthEdge<T> = Edge<LinearProgramNode<T>, ()>;

#[derive(Clone, Copy)]
pub struct SynthesizerState<'a, T: TypeSystemBounds> {
    pub ecta: &'a SynthEcta<T>,
    pub inverse_map: &'a InverseMap<T>,
    pub bool_fragments: &'a Vec<&'a Fragment<T>>,
}

impl<'a, T: TypeSystemBounds> SynthesizerState<'a, T> {
    pub fn new(
        ecta: &'a ECTA<SynthEctaEdge<T>, ()>,
        inverse_map: &'a InverseMap<T>,
        bool_fragments: &'a Vec<&'a Fragment<T>>,
    ) -> Self {
        Self {
            ecta,
            inverse_map,
            bool_fragments,
        }
    }
}

fn create_ecta_from_traces<T: TypeSystemBounds>(
    ecta: &mut ECTA<SynthEctaEdge<T>, ()>,
    frags: &[&Program<T>],
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
            let ty_edge = SynthEctaEdge::T(g[0].get_type());

            let type_node =
                ecta.add_node(Node::new(), vec![(ty_edge, None, vec![ecta.empty_node])]);

            let mut node_collector = vec![type_node];
            if let ProgramNode::Operation(_) = g[0].node {
                let x = g
                    .iter()
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

fn deduce2<T: TypeSystemBounds>(
    state: SynthesizerState<T>,
    node: ECTANode,
    hole: Examples,
    target_type: T,
) -> Option<Program<T>> {
    info!("start deduction");
    if node == state.ecta.empty_node {
        warn!("Empty node in deduce");
        panic!();
    }

    let initial = SketchWithData::from_hole(target_type, node, hole);

    info!("Initial sketch = {initial}");

    let mut queue = MinHeap::new();
    queue.push(initial);

    while let Some(sketch) = queue.pop() {
        info!("Sketch in consideration = {sketch}");
        for s in sketch.fill_hole(&state, state.inverse_map) {
            if s.is_complete() {
                info!("Complete sketch = {s}");
                return s.try_into().ok();
            } else {
                info!("Pushed sketch onto the queue = {s}");
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
    hole: Examples,
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
    let bool_fragments = fragment_collection.get_all_sorted(&BaseType::Bool);

    let synthesis_state = SynthesizerState::new(&ecta, inverse_map, &bool_fragments);

    let prog_iter = deduce2(synthesis_state, top_node, hole.clone(), target_type);

    prog_iter.filter(|p| p.passes_all_test_cases(&hole))
}

pub fn synthesis(
    sig: Signature<BaseType>,
    l: &Libraries<BaseType>,
    tests: Examples,
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
            ty: *ty,
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
        let traces: Vec<&Fragment<BaseType>> = frags.find_valid_traces(&tests);

        info!("Printing traces of up to size {}", frags.get_size());
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
            if frags.get_size() > MAX_FRAG_SIZE {
                eprintln!("We failed to synthesize anything in a bound of size 10");
                return None;
            }
        }
    }
}
