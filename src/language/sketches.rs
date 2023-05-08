use std::{cmp::Ordering, fmt::Display, iter::once};

use ecta_rs::ECTANode;
use itertools::Itertools;
use log::info;

use crate::{
    data_structures::{InverseMap, MinHeap},
    types::{BaseType, RefinementType, TypeSystemBounds},
    SynthEctaEdge, SynthEdge, SynthesizerState, IF_DEPTH,
};

use super::{
    Constant, Examples, LinearProgramNode, Operation, Program, ProgramNode, TestCase, Variable,
};

/// A sketch is a program that can contain holes in it
/// Each hole has a corresponding type it is trying to fill
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sketch<T: TypeSystemBounds> {
    Hole(T),
    Constant(Constant),
    Variable(Variable<T>, T),
    Operation(Operation<T>, Vec<Sketch<T>>),
    If(Box<Program<T>>, Box<Sketch<T>>, Box<Sketch<T>>),
}

impl<T: TypeSystemBounds> Sketch<T> {
    fn is_consistent(&self, e: &Examples, inverse_map: &InverseMap<T>) -> bool {
        match self {
            Sketch::Hole(_) => true,
            Sketch::Constant(c) => e.iter().all(|TestCase { output, .. }| output == c),
            Sketch::Variable(v, t) => e
                .iter()
                .all(|t| t.into_env().get(v).map(|c| c == &t.output).unwrap_or(false)),
            Sketch::Operation(o, args) => args
                .iter()
                .zip(e.witness_examples(o, inverse_map).into_iter())
                .all(|(a, e_vec)| {
                    e_vec
                        .into_iter()
                        .any(|e_single| a.is_consistent(&e_single, inverse_map))
                }),
            Sketch::If(b, s1, s2) => {
                s1.is_consistent(
                    &e.filter_behavior(*b.clone(), |c| c == &Constant::Bool(true)),
                    inverse_map,
                ) && s2.is_consistent(
                    &e.filter_behavior(*b.clone(), |c| c == &Constant::Bool(false)),
                    inverse_map,
                )
            }
        }
    }
}

impl From<&Sketch<BaseType>> for BaseType {
    fn from(s: &Sketch<BaseType>) -> Self {
        match s {
            Sketch::Hole(t) => *t,
            Sketch::Constant(c) => c.clone().into(),
            Sketch::Variable(_, t) => *t,
            Sketch::Operation(o, _) => o.sig.output,
            Sketch::If(_, t1, t2) => {
                let t: BaseType = (&**t1).into();
                assert!(t == (&**t2).into());
                t
            }
        }
    }
}

impl From<&Sketch<RefinementType>> for RefinementType {
    fn from(s: &Sketch<RefinementType>) -> Self {
        match s {
            Sketch::Hole(t) => t.clone(),
            Sketch::Constant(c) => c.clone().into(),
            Sketch::Variable(_, t) => t.clone(),
            Sketch::Operation(o, _) => o.sig.output.clone(),
            Sketch::If(_, t1, t2) => {
                let t: RefinementType = (&**t1).into();
                assert!(t == (&**t2).into());
                t
            }
        }
    }
}

impl<T: TypeSystemBounds> From<Program<T>> for Sketch<T> {
    fn from(Program { node, args }: Program<T>) -> Self {
        match node {
            ProgramNode::Constant(c) => Self::Constant(c),
            ProgramNode::Variable(v, t) => Sketch::Variable(v, t),
            ProgramNode::Operation(o) => {
                Self::Operation(o, args.into_iter().map(Self::from).collect_vec())
            }
            ProgramNode::If => {
                assert!(args.len() == 3);
                Self::If(
                    Box::new(args[0].clone().into()),
                    Box::new(args[1].clone().into()),
                    Box::new(args[2].clone().into()),
                )
            }
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<Sketch<T>> for Program<T> {
    type Error = ();

    fn try_from(value: Sketch<T>) -> Result<Self, Self::Error> {
        match value {
            Sketch::Hole(_) => Err(()),
            Sketch::Constant(c) => Ok(Program {
                node: ProgramNode::Constant(c),
                args: Vec::new(),
            }),
            Sketch::Variable(v, t) => Ok(Program {
                node: ProgramNode::Variable(v, t),
                args: Vec::new(),
            }),
            Sketch::Operation(o, args) => Ok(Program {
                node: ProgramNode::Operation(o),
                args: args.into_iter().try_fold(Vec::new(), |mut acc, a| {
                    acc.push(a.try_into()?);
                    Ok(acc)
                })?,
            }),
            Sketch::If(b, s1, s2) => Ok(Program {
                node: ProgramNode::If,
                args: vec![*b, (*s1).try_into()?, (*s2).try_into()?],
            }),
        }
    }
}

impl<T: TypeSystemBounds> Display for Sketch<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Sketch::Hole(t) => write!(f, "{{}} : {t:?}"),
            Self::Constant(c) => write!(f, "{c}"),
            Self::Variable(v, _) => write!(f, "{v}"),
            Self::Operation(o, args) => {
                write!(f, "{o}({})", args.iter().map(ToString::to_string).join(","))
            }
            Self::If(cond, s1, s2) => write!(f, "if ({cond}) {{{s1}}} else {{{s2}}}"),
        }
    }
}

impl<T: TypeSystemBounds> PartialOrd for Sketch<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(match (self, other) {
            // Handle equal cases first
            (Sketch::Hole(_), Sketch::Hole(_))
            | (Sketch::Constant(_), Sketch::Constant(_))
            | (Sketch::Variable(..), Sketch::Variable(..)) => Ordering::Equal,

            // Equal program nodes, but maybe not equal sketches
            (Sketch::Operation(_, args1), Sketch::Operation(_, args2)) => {
                // If they arr both empty, they are equal
                if args1.is_empty() && args2.is_empty() {
                    Ordering::Equal
                // If they have an unequal number of arguments, choose the lesser one
                } else if args1.len().cmp(&args2.len()) != Ordering::Equal {
                    args1.len().cmp(&args2.len())
                // Otherwise, compare the arguments
                } else {
                    args1.partial_cmp(args2).unwrap()
                }
            }
            (Sketch::If(c1, t1, f1), Sketch::If(c2, t2, f2)) => {
                let mut res = c1.partial_cmp(c2).unwrap();
                if res == Ordering::Equal {
                    res = t1.partial_cmp(t2).unwrap();
                    if res == Ordering::Equal {
                        res = f1.partial_cmp(f2).unwrap()
                    }
                };
                res
            }

            // Then choose variables first
            (Sketch::Variable(..), _) => Ordering::Less,
            (_, Sketch::Variable(..)) => Ordering::Greater,

            // Then choose constants to help fail fast?
            (Sketch::Constant(_), _) => Ordering::Less,
            (_, Sketch::Constant(_)) => Ordering::Greater,

            // The try to fill in holes
            (Sketch::Hole(_), _) => Ordering::Less,
            (_, Sketch::Hole(_)) => Ordering::Greater,

            // Then we prioritize operations over if's I guess?
            // Since forward progress should help us terminate faster
            (Sketch::Operation(..), Sketch::If(..)) => Ordering::Less,
            (Sketch::If(..), Sketch::Operation(..)) => Ordering::Greater,
        })
    }
}

impl<T: TypeSystemBounds> Ord for Sketch<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// Information relating to a hole in a sketch
/// There can be more than one hole in a sketch, this is just the information to one of them
/// Each hole data must be unqiue
#[derive(Clone)]
pub struct HoleMetaData<T: TypeSystemBounds> {
    /// The path threw the sketch to get to this hole
    path: Vec<u8>,
    /// The corresponding nodeid in the ECTA
    nodeid: ECTANode,
    /// Any input/output examples the hole should follow
    examples: Examples,
    /// The type of the hole
    typ: T,
    /// How many if statements that one needs to go through to get to this hole
    /// If number is >= `IF_DEPTH` then we can't synthesize an if statement for this hole
    if_depth: usize,
    /// Whether or not there can be a recursive call in this hole
    recursion_allowed: bool,
}

impl<T: TypeSystemBounds> PartialEq for HoleMetaData<T> {
    fn eq(&self, other: &Self) -> bool {
        self.path == other.path
    }
}

impl<T: TypeSystemBounds> Eq for HoleMetaData<T> {}

impl<T: TypeSystemBounds> PartialOrd for HoleMetaData<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.path.len().partial_cmp(&other.path.len())
    }
}

impl<T: TypeSystemBounds> Ord for HoleMetaData<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<T: TypeSystemBounds> HoleMetaData<T> {
    fn new(nodeid: ECTANode, examples: Examples, ty: T) -> Self {
        HoleMetaData {
            path: Vec::new(),
            nodeid,
            examples,
            typ: ty,
            if_depth: 0,
            recursion_allowed: false,
        }
    }

    fn inc_if(self) -> Self {
        Self {
            if_depth: self.if_depth + 1,
            ..self
        }
    }

    fn allow_recursion(self) -> Self {
        Self {
            recursion_allowed: true,
            ..self
        }
    }

    fn add_depth(self, p: u8) -> Self {
        Self {
            path: [self.path, vec![p]].concat(),
            ..self
        }
    }

    fn get_edge_candidates(&self, state: &SynthesizerState<T>) -> Vec<SketchWithData<T>> {
        if self.nodeid == state.ecta.empty_node {
            info!("The empty node has no candidates");

            return Vec::new();
        }

        let edges: Vec<_> = state
            .ecta
            .get_edges(self.nodeid)
            .filter_map(|e| {
                if matches!(e.data, SynthEctaEdge::T(_)) {
                    None
                } else {
                    Some(e.clone().map(|s| match s {
                        SynthEctaEdge::P(p) => p,
                        _ => unreachable!(),
                    }))
                }
            })
            .collect();

        if edges.is_empty() {
            info!("No edge candidates");
            return Vec::new();
        }

        let iterable: Vec<_> = edges
            .into_iter()
            .sorted_by(|a, b| a.data.cmp(&b.data))
            .group_by(|edge| edge.data.clone())
            .into_iter()
            .map(|(k, v)| {
                (
                    k,
                    v.into_iter()
                        .sorted_by(|p1, p2| p1.edge_num.cmp(&p2.edge_num))
                        .collect_vec(),
                )
            })
            .collect();

        iterable
            .into_iter()
            .flat_map(|(p_node, edges)| match p_node {
                LinearProgramNode::Constant(c) => vec![SketchWithData::from_constant(c)],
                LinearProgramNode::Variable(v, ty) => vec![SketchWithData::from_variable(v, ty)],
                LinearProgramNode::Operation(o) => {
                    SketchWithData::from_operation(o, edges, self, state.inverse_map)
                }
            })
            .collect()
    }
}

/// Sketches with their corresponding hole data
pub struct SketchWithData<T: TypeSystemBounds> {
    sketch: Sketch<T>,
    holes: MinHeap<HoleMetaData<T>>,
}

impl<T: TypeSystemBounds> Display for SketchWithData<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", self.sketch)
    }
}

impl<T: TypeSystemBounds> PartialEq for SketchWithData<T> {
    fn eq(&self, other: &Self) -> bool {
        self.sketch == other.sketch
    }
}

impl<T: TypeSystemBounds> Eq for SketchWithData<T> {}

impl<T: TypeSystemBounds> PartialOrd for SketchWithData<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.sketch.partial_cmp(&other.sketch)
    }
}

impl<T: TypeSystemBounds> Ord for SketchWithData<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<T: TypeSystemBounds> TryFrom<SketchWithData<T>> for Program<T> {
    type Error = ();

    fn try_from(value: SketchWithData<T>) -> Result<Self, Self::Error> {
        value.sketch.try_into()
    }
}

impl<'a, T: TypeSystemBounds + 'a> SketchWithData<T> {
    pub fn from_hole(ty: T, nodeid: ECTANode, examples: Examples) -> Self {
        let mut holes = MinHeap::new();
        holes.push(HoleMetaData::new(nodeid, examples, ty.clone()));
        Self {
            sketch: Sketch::Hole(ty),
            holes,
        }
    }

    pub fn from_constant(c: Constant) -> Self {
        Self {
            sketch: Sketch::Constant(c),
            holes: MinHeap::new(),
        }
    }

    pub fn from_variable(v: Variable<T>, ty: T) -> Self {
        Self {
            sketch: Sketch::Variable(v, ty),
            holes: MinHeap::new(),
        }
    }

    pub fn from_operation(
        o: Operation<T>,
        edges: Vec<SynthEdge<T>>,
        holedata: &HoleMetaData<T>,
        inverse_map: &InverseMap<T>,
    ) -> Vec<Self> {
        let args: Vec<_> = o
            .sig
            .input
            .iter()
            .map(|t| Sketch::Hole(t.clone()))
            .collect();
        let examples_vec = holedata.examples.witness_examples(&o, inverse_map);
        examples_vec
            .into_iter()
            .map(|examples_v| {
                let holes = o
                    .sig
                    .input
                    .iter()
                    .zip(examples_v)
                    .zip(edges.iter())
                    .map(|((t, examples), e)| HoleMetaData {
                        path: vec![e.edge_num],
                        examples,
                        nodeid: e.nodeidx,
                        typ: t.clone(),
                        if_depth: holedata.if_depth,
                        recursion_allowed: holedata.recursion_allowed,
                    })
                    .collect();
                SketchWithData {
                    sketch: Sketch::Operation(o.clone(), args.clone()),
                    holes,
                }
            })
            .collect()
    }

    /// The goal of this function is to create a closure that produces sketches
    /// Then you can fill the hole
    fn sketch_constructor(
        self,
        path: std::slice::Iter<'a, u8>,
    ) -> impl Fn(SketchWithData<T>) -> SketchWithData<T> + 'a {
        move |x| -> SketchWithData<T> {
            let path = path.clone();
            let sketch = self.sketch.clone();
            fn helper<T: TypeSystemBounds>(
                x: SketchWithData<T>,
                mut path: std::slice::Iter<u8>,
                sketch: Sketch<T>,
            ) -> SketchWithData<T> {
                if path.is_empty() {
                    x
                } else {
                    let i = *path.next().unwrap();
                    match sketch {
                        Sketch::Hole(_) | Sketch::Constant(_) | Sketch::Variable(..) => panic!(),
                        Sketch::Operation(o, mut args) => {
                            let SketchWithData { sketch, holes } =
                                helper(x, path, args[i as usize].clone());
                            args[i as usize] = sketch;

                            let holes = holes.into_iter().map(|h| h.add_depth(i)).collect();

                            SketchWithData {
                                sketch: Sketch::Operation(o, args),
                                holes,
                            }
                        }
                        Sketch::If(b, mut t1, mut f1) => {
                            let (holes, t1, f1) = match i {
                                0 => {
                                    /* *b = sketch; */
                                    unreachable!()
                                }
                                1 => {
                                    let SketchWithData { sketch, holes } = helper(x, path, *t1);
                                    *t1 = sketch;
                                    (
                                        holes
                                            .into_iter()
                                            .map(|h| h.add_depth(1).inc_if())
                                            .collect(),
                                        t1,
                                        f1,
                                    )
                                }
                                2 => {
                                    let SketchWithData { sketch, holes } = helper(x, path, *f1);
                                    *f1 = sketch;
                                    (
                                        holes
                                            .into_iter()
                                            .map(|h: HoleMetaData<_>| {
                                                h.add_depth(2).inc_if().allow_recursion()
                                            })
                                            .collect(),
                                        t1,
                                        f1,
                                    )
                                }
                                _ => unreachable!(),
                            };

                            SketchWithData {
                                sketch: Sketch::If(b, t1, f1),
                                holes,
                            }
                        }
                    }
                }
            }
            helper(x, path, sketch)
        }
    }

    fn create_if_sketch(
        &self,
        state: &SynthesizerState<T>,
        holedata: &HoleMetaData<T>,
    ) -> Vec<Self> {
        state
            .bool_fragments
            .iter()
            .map(|b| {
                let new_hole = holedata.clone().add_depth(1).inc_if();
                let holes = self
                    .holes
                    .clone()
                    .into_iter()
                    .map(|h| h.add_depth(1))
                    .chain(once(new_hole))
                    .collect();
                Self {
                    sketch: Sketch::If(
                        Box::new(b.fragment.clone().into()),
                        Box::new(self.sketch.clone()),
                        Box::new(Sketch::Hole(holedata.typ.clone())),
                    ),
                    holes,
                }
            })
            .collect()
    }

    pub fn fill_hole(
        mut self,
        state: &SynthesizerState<T>,
        inverse_map: &InverseMap<T>,
    ) -> Vec<Self> {
        assert!(!self.is_complete());
        // What do you need to fill a sketch?
        // Where is the hole?
        // What can I fill it with?
        // Sketch has a spine to the location of the hole
        // Sketch has a node in the ecta

        let holedata = self.holes.pop().unwrap();

        // walk to the hole,
        // then construct new ones with the hole filled(possibly with new holes)
        let f = self.sketch_constructor(holedata.path.iter());

        let mut candidates = holedata.get_edge_candidates(state);

        candidates = if holedata.if_depth < IF_DEPTH {
            candidates.into_iter().fold(Vec::new(), |mut acc, x| {
                acc.extend(x.create_if_sketch(state, &holedata));
                acc.push(x);
                acc
            })
        } else {
            candidates
        };

        dbg!(candidates
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>());

        dbg!(&holedata.examples);

        let sketches: Vec<_> = candidates
            .into_iter()
            .filter(|s| s.sketch.is_consistent(&holedata.examples, inverse_map))
            .map(f)
            .collect();

        dbg!(sketches.iter().map(ToString::to_string).collect::<Vec<_>>());
        /*

            state.recursion_allowed;

            // If recursive call, check extra consistency
            todo!();
        */
        sketches
    }

    pub fn is_complete(&self) -> bool {
        self.holes.is_empty()
    }
}
