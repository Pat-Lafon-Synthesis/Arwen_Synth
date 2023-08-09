use std::{collections::HashMap, fmt::Display, iter::once};

use ecta_rs::ECTANode;
use itertools::Itertools;
use log::{info, warn};

use crate::{
    data_structures::{Fragment, InverseMap, MinHeap, SynthCostFunc},
    BaseType, RefinementType, SynthEcta, SynthEctaEdge, SynthesizerState, TypeSystemBounds,
    IF_DEPTH,
};

use super::{
    Constant, Environment, Examples, LinearProgram, LinearProgramNode, Operation, Program,
    ProgramNode, TestCase, Variable,
};

/// A sketch is a program that can contain holes in it
/// Each hole has a corresponding type it is trying to fill
#[derive(Debug, Clone /* , PartialEq, Eq */)]
pub enum Sketch<T: TypeSystemBounds> {
    Hole(T),
    Constant(Constant),
    Variable(Variable<T>),
    Operation(Operation<T>, Vec<Sketch<T>>),
    If(Box<Program<T>>, Box<Sketch<T>>, Box<Sketch<T>>),
    Rec(T, Vec<Sketch<T>>),
}

impl<T: TypeSystemBounds> Sketch<T> {
    /// A second, hopefully cleaner attempt at example and block consistency
    /// Think of this like a symbolic interpreter
    fn symbolic_block_based_evaluator(
        &self,
        e: &Examples,
        state: &SynthesizerState<T>,
        current_node: ECTANode,
        full_sketch: &Self,
    ) -> bool {
        /*         info!("Sketch in symbolic evaluator: {self}");
        info!("Current_node in symbolic evaluator: {current_node:?}"); */
        self.symbolic_block_based_evaluator_helper(
            e,
            state,
            current_node,
            full_sketch,
            None,
            &mut HashMap::new(),
        )
    }

    fn symbolic_block_based_evaluator_helper(
        &self,
        e: &Examples,
        state: &SynthesizerState<T>,
        current_node: ECTANode,
        full_sketch: &Self,
        last_rec_arg: Option<&Constant>,
        // Hold lazy evaluation of arguments to operations
        env: &mut HashMap<String, LinearProgram<T>>,
    ) -> bool {
        // Should examples be non-empty?
        // Maybe only when we are not in a recursive call?
        if e.is_empty() {
            warn!("For the moment we are allow empty sets of examples");
            info!("\t{self}\n\t{full_sketch}");
            return true;
        }

        // Enforcing block consistency so can't be outside of the ECTA
        assert!(current_node != state.ecta.empty_node);
        match self {
            Sketch::Hole(_) => {
                // There is a question about reachability
                // Given that this hole could be filled with anything, is there any set of output values that would not be reconcilable with this hole
                // I think the answer is no, because the set of reachable constants is explored starting with input variables and grown via each of the components.
                // Thus the only way we know about a constant is if we reached it during fragment creation.
                true
            }
            Sketch::Constant(c) => {
                // This seems pretty easy
                // All examples should just return the output constant
                // And I guess the constant should be in the block
                if !e.is_consistent_with(|TestCase { output, .. }| output == c) {
                    /* info!("We rejected a sketch because the constants didn't line up with the test cases"); */
                    false
                } else if LinearProgramNode::Constant(c.clone())
                    .ecta_next_program_nodes(state.ecta, current_node)
                    .is_none()
                {
                    /* info!("We rejected a sketch because the constant was not in the ecta"); */
                    false
                } else {
                    true
                }
            }
            Sketch::Variable(v @ Variable { name, .. }) => {
                // The variable ends up being a little trickier because we should check the enviroment first
                if let Some(p) = env.get(name) {
                    Sketch::from(p.clone()).symbolic_block_based_evaluator_helper(
                        e,
                        state,
                        current_node,
                        full_sketch,
                        last_rec_arg,
                        env,
                    )
                } else {
                    if !e.is_consistent_with(|t| {
                        Into::<Environment<T>>::into(t)
                            .get(v)
                            .map(|c| c == &t.output)
                            .unwrap_or(false)
                    }) {
                        /* info!("We rejected a sketch because the variable didn't line up with the test cases"); */
                        false
                    } else if LinearProgramNode::Variable(v.clone())
                        .ecta_next_program_nodes(state.ecta, current_node)
                        .is_none()
                    {
                        /* info!("We rejected a sketch because the variable was not in the ecta"); */
                        false
                    } else {
                        true
                    }
                }
            }
            Sketch::If(b, s1, s2) => {
                let b = b.substitute(env);
                if !b.get_behavior(e.get_positive_examples()).len()
                    == e.get_positive_examples().len()
                {
                    /* info!("We rejected a sketch because the behaviour of the positive examples was incomplete"); */
                    false
                } else if !b.get_behavior(e.get_negative_examples()).len()
                    == e.get_negative_examples().len()
                {
                    /* info!("We rejected a sketch because the behaviour of the negative examples was incomplete"); */
                    false
                } else if !s1.symbolic_block_based_evaluator_helper(
                    &e.filter_behavior_p(&b, &|c| c == &Constant::Bool(true)),
                    state,
                    current_node,
                    full_sketch,
                    last_rec_arg,
                    env,
                ) {
                    /* info!("We rejected a sketch because the positive branch was not consistent"); */
                    false
                } else if !s2.symbolic_block_based_evaluator_helper(
                    &e.filter_behavior_p(&b, &|c| c == &Constant::Bool(false)),
                    state,
                    current_node,
                    full_sketch,
                    last_rec_arg,
                    env,
                ) {
                    /* info!("We rejected a sketch because the negative branch was not consistent: {full_sketch}"); */
                    false
                } else {
                    true
                }
            }
            Sketch::Operation(o, args) => {
                // Maybe the operation is fully complete
                if let Ok(p) =
                    // todo Patrick for real, You need to worry about Rec here, only do linear where you can solve it immediately
                    TryInto::<Program<T>>::try_into(self.clone())
                        .and_then(|p| TryInto::<LinearProgram<T>>::try_into(p))
                {
                    if !e.is_consistent_with(|t @ TestCase { output, .. }| {
                        if let Ok(c) = p.interpret(&t.into()) {
                            c == *output
                        } else {
                            false
                        }
                    }) {
                        /* info!("We rejected a sketch because the operation didn't line up with the test cases"); */
                        false
                    } else {
                        // There is nothing more to synthesize here so we are probably fine block-consistencywise
                        true
                    }
                } else {
                    // There are still holes in the sketch
                    let product_vec_examples = e.witness_examples(o, state.inverse_map);
                    if product_vec_examples.is_none() {
                        /* info!("We rejected a sketch because it didn't have a complete inverse semantics: {self}"); */
                        return false;
                    }

                    let product_vec_examples = product_vec_examples.unwrap();

                    if let Some(edges) = LinearProgramNode::Operation(o.clone())
                        .ecta_next_program_nodes(state.ecta, current_node)
                    {
                        let res = args.iter().enumerate().zip(product_vec_examples).all(
                            |((idx, a), e_vec)| {
                                e_vec.into_iter().any(|e_single| {
                                    a.symbolic_block_based_evaluator_helper(
                                        &e_single,
                                        state,
                                        edges[idx],
                                        full_sketch,
                                        last_rec_arg,
                                        env,
                                    )
                                })
                            },
                        );
                        if !res {
                            /* info!("We rejected a sketch because the arguments were not consistent {self}"); */
                        }
                        res
                    } else {
                        /* info!("We rejected a sketch because of a lack of traces: {self}");
                        info!("{e}");
                        info!("{:?}", state.start_node);
                        info!("{}", o.name);
                        info!("{current_node:?}");
                        info!("{}", state.ecta.get_dot(&[])); */
                        false
                    }
                }
            }
            Sketch::Rec(_t, args) => {
                // Convert args from sketches to programs
                let processed_args: Vec<LinearProgram<T>> = args.into_iter().map(|s| s.clone().try_into().unwrap())
                // Substitute in an the environment
                .map(|p: Program<T>| p.substitute(env))
                // Convert from programs to linear programs
                .map(|p| p.try_into().unwrap()).collect();
                // Check that given the current examples, all input values are valid
                if processed_args
                    .iter()
                    .try_for_each(|l| {
                        if e.is_consistent_with(|t| {
                            l.interpret(&Into::<Environment<T>>::into(t)).is_ok()
                        }) {
                            Ok(())
                        } else {
                            eprintln!(
                                "Inconsistency in recursive arguments:\n\t {full_sketch}\n\t{e:?}"
                            );
                            Err(())
                        }
                    })
                    .err()
                    .is_some()
                {
                    /* info!(
                        "We rejected a sketch because the recursive arguments were not consistent"
                    ); */
                    return false;
                }
                let helper = |tests: &[TestCase]| {
                    tests
                        .iter()
                        .map(|t @ TestCase { output, .. }| {
                            let env = Into::<Environment<T>>::into(t);
                            let new_inputs = processed_args
                                .iter()
                                .map(|l| l.interpret(&env).unwrap())
                                .collect_vec();
                            TestCase {
                                inputs: new_inputs,
                                output: output.clone(),
                            }
                        })
                        .collect()
                };

                // Create new examples
                let new_examples = Examples::new(
                    helper(e.get_positive_examples()),
                    helper(e.get_negative_examples()),
                );

                // And are decreasing?
                // todo, all examples or just the positive ones?
                let rec_arg = new_examples
                    .get_positive_examples()
                    .iter()
                    .map(|TestCase { inputs, .. }| &inputs[0])
                    .max()
                    .unwrap();

                let new_rec_arg = if let Some(r) = last_rec_arg {
                    if r < &rec_arg {
                        /* info!("We rejected a rec sketch because it didn't have a decreasing semantics: {self}"); */
                        return false;
                    } else {
                        Some(rec_arg)
                    }
                } else {
                    Some(rec_arg)
                };

                let mut new_env = processed_args
                    .into_iter()
                    .enumerate()
                    .map(|(i, val)| (format!("args{i}"), val))
                    .collect();

                /* info!(
                    "Current state: {}",
                    format!("{full_sketch}\n{e}\n{new_examples}\n{current_node:?}\n\n")
                ); */

                // All the examples have the corresponding outputs we are looking for I think
                full_sketch.symbolic_block_based_evaluator_helper(
                    &new_examples,
                    state,
                    current_node,
                    full_sketch,
                    new_rec_arg,
                    &mut new_env,
                )
            }
        }
    }
}

impl<T: TypeSystemBounds> Sketch<T> {
    /* fn is_example_consistent_helper(
        &self,
        e: &Examples,
        state: &SynthesizerState<T>,
        current_node: ECTANode,
        full_sketch: (&Self, &Examples),
        last_rec_arg: Option<&Constant>,
    ) -> bool {
        match self {
            Sketch::Hole(_) => {
                let res = current_node != state.ecta.empty_node;
                if !res {
                    info!("We rejected a sketch because of a lack of traces: {self}")
                }
                res
            }
            Sketch::Constant(c) => {
                e.is_consistent_with(|TestCase { output, .. }| output == c)
                    && LinearProgramNode::Constant(c.clone())
                        .ecta_next_program_nodes(state.ecta, current_node)
                        .is_some()
            }
            Sketch::Variable(v) => {
                e.is_consistent_with(|t| {
                    Into::<Environment<T>>::into(t)
                        .get(v)
                        .map(|c| c == &t.output)
                        .unwrap_or(false)
                }) && LinearProgramNode::Variable(v.clone())
                    .ecta_next_program_nodes(state.ecta, current_node)
                    .is_some()
            }
            Sketch::Operation(o, args) => {
                if let Some(edges) = LinearProgramNode::Operation(o.clone())
                    .ecta_next_program_nodes(state.ecta, current_node)
                {
                    if args.is_empty() {
                        let p = Program {
                            node: ProgramNode::Operation(o.clone()),
                            args: vec![],
                        };
                        let res = p.interpret(&Environment::new(), &p).unwrap();

                        e.is_consistent_with(|TestCase { output, .. }| output == &res)
                    } else {
                        info!("Current thing: {self}");
                        info!("Current examples: {e:?}");
                        let product_vec_examples =
                            e.witness_examples(o, state.inverse_map).unwrap();

                        if product_vec_examples.is_empty() {
                            info!("We rejected a sketch because it didn't have a complete inverse semantics: {self}");
                            return false;
                        }

                        args.iter().enumerate().zip(product_vec_examples).all(
                            |((idx, a), e_vec)| {
                                e_vec.into_iter().any(|e_single| {
                                    a.is_example_consistent_helper(
                                        &e_single,
                                        state,
                                        edges[idx],
                                        full_sketch,
                                        last_rec_arg,
                                    )
                                })
                            },
                        )
                    }
                } else {
                    info!("We rejected a sketch because of a lack of traces: {self}");
                    false
                }
            }
            Sketch::If(b, s1, s2) => {
                // Check that all the different examples bool is evaluated in have valid outputs
                b.get_behavior(e.get_positive_examples()).len() == e.get_positive_examples().len()
                    && b.get_behavior(e.get_negative_examples()).len()
                        == e.get_negative_examples().len()
                        // And that each of the branches are consistent with the examples
                    && s1.is_example_consistent_helper(
                        &e.filter_behavior_p(b, &|c| c == &Constant::Bool(true)),
                        state,
                        current_node,
                        full_sketch,
                        last_rec_arg
                    )
                    && s2.is_example_consistent_helper(
                        &e.filter_behavior_p(b, &|c| c == &Constant::Bool(false)),
                        state,
                        current_node,
                        full_sketch,
                        last_rec_arg
                    )
            }
            Sketch::Rec(_t, args) => {
                info!("Check that rec is consistent");

                let p = TryInto::<Program<T>>::try_into(args[0].clone()).unwrap();
                let first_args = e
                    .get_positive_examples()
                    .iter()
                    .map(|t| p.interpret(&t.into(), &p).ok())
                    .collect_vec();

                if first_args.iter().any(|x| x.is_none()) {
                    info!("We rejected a rec sketch because it was invalid for it's recursive argument(the first arg): {self}");
                    return false;
                }

                // todo I did the simple thing that says that one example upper bounds all the others, and I need to ensure that the the upper bound is always decreasing
                let rec_arg = first_args
                    .into_iter()
                    .map(|x| x.unwrap())
                    .max_by(|x, y| match (x, y) {
                        (Constant::Int(x), Constant::Int(y)) => x.cmp(y),
                        (Constant::IntList(x), Constant::IntList(y)) => x.len().cmp(&y.len()),
                        (Constant::IntTree(x), Constant::IntTree(y)) => x.height().cmp(&y.height()),
                        _ => todo!(),
                    })
                    .unwrap();
                if last_rec_arg.is_some() && last_rec_arg.unwrap() < &rec_arg {
                    info!("We rejected a rec sketch because it didn't have a decreasing semantics: {self}");
                    return false;
                }

                info!("TODO: we could do something smarter to ensure example consistency");
                true
            }
        }
    }

    fn is_example_consistent(
        &self,
        e: &Examples,
        state: &SynthesizerState<T>,
        current_node: ECTANode,
        full_sketch: (&Self, &Examples),
    ) -> bool {
        self.is_example_consistent_helper(e, state, current_node, full_sketch, None)
    } */
}

impl From<&Sketch<BaseType>> for BaseType {
    fn from(s: &Sketch<BaseType>) -> Self {
        match s {
            Sketch::Hole(t) => *t,
            Sketch::Constant(c) => c.clone().into(),
            Sketch::Variable(v) => v.ty,
            Sketch::Operation(o, _) => o.sig.output,
            Sketch::If(_, t1, t2) => {
                let t: BaseType = (&**t1).into();
                assert!(t == (&**t2).into());
                t
            }
            Sketch::Rec(t, _) => *t,
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<&Sketch<T>> for ProgramNode<T> {
    type Error = ();

    fn try_from(value: &Sketch<T>) -> Result<Self, Self::Error> {
        match value {
            Sketch::Hole(_) => Err(()),
            Sketch::Constant(c) => Ok(ProgramNode::Constant(c.clone())),
            Sketch::Variable(v) => Ok(ProgramNode::Variable(v.clone())),
            Sketch::Operation(o, ..) => Ok(ProgramNode::Operation(o.clone())),
            Sketch::If(..) => Ok(ProgramNode::If),
            Sketch::Rec(..) => Err(()),
        }
    }
}

impl From<&Sketch<RefinementType>> for RefinementType {
    fn from(s: &Sketch<RefinementType>) -> Self {
        match s {
            Sketch::Hole(t) => t.clone(),
            Sketch::Constant(c) => c.clone().into(),
            Sketch::Variable(v) => v.ty.clone(),
            Sketch::Operation(o, _) => o.sig.output.clone(),
            Sketch::If(_, t1, t2) => {
                let t: RefinementType = (&**t1).into();
                assert!(t == (&**t2).into());
                t
            }
            Sketch::Rec(t, _) => t.clone(),
        }
    }
}

impl<T: TypeSystemBounds> From<Program<T>> for Sketch<T> {
    fn from(Program { node, args }: Program<T>) -> Self {
        match node {
            ProgramNode::Constant(c) => Self::Constant(c),
            ProgramNode::Variable(v) => Sketch::Variable(v),
            ProgramNode::Operation(o) => {
                Self::Operation(o, args.into_iter().map(Self::from).collect_vec())
            }
            ProgramNode::Rec(t) => Self::Rec(t, args.into_iter().map(Self::from).collect_vec()),
            ProgramNode::If => {
                assert!(args.len() == 3);
                Self::If(
                    Box::new(args[0].clone()),
                    Box::new(args[1].clone().into()),
                    Box::new(args[2].clone().into()),
                )
            }
        }
    }
}

impl<T: TypeSystemBounds> From<LinearProgram<T>> for Sketch<T> {
    fn from(value: LinearProgram<T>) -> Self {
        Program::from(value).into()
    }
}

impl<T: TypeSystemBounds> From<Fragment<T>> for Sketch<T> {
    fn from(Fragment { fragment, .. }: Fragment<T>) -> Self {
        Program::from(fragment).into()
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
            Sketch::Variable(v) => Ok(Program {
                node: ProgramNode::Variable(v),
                args: Vec::new(),
            }),
            Sketch::Operation(o, args) => Ok(Program {
                node: ProgramNode::Operation(o),
                args: args.into_iter().try_fold(Vec::new(), |mut acc, a| {
                    acc.push(a.try_into()?);
                    Ok(acc)
                })?,
            }),
            Sketch::Rec(t, args) => Ok(Program {
                node: ProgramNode::Rec(t),
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
            Self::Variable(v) => write!(f, "{v}"),
            Self::Operation(o, args) => {
                write!(f, "{o}({})", args.iter().map(ToString::to_string).join(","))
            }
            Self::Rec(t, args) => {
                write!(
                    f,
                    "rec<{t:?}>({})",
                    args.iter().map(ToString::to_string).join(",")
                )
            }
            Self::If(cond, s1, s2) => write!(f, "if ({cond}) {{{s1}}} else {{{s2}}}"),
        }
    }
}

impl<T: TypeSystemBounds> SynthCostFunc for Sketch<T> {
    fn cost(&self) -> usize {
        match self {
            Sketch::Variable(_) => 1,
            Sketch::Constant(_) => 2,
            Sketch::Hole(_) => 2,
            Sketch::Operation(_, args) => 3 + args.iter().map(SynthCostFunc::cost).sum::<usize>(),
            Sketch::If(c, t, f) => 4 + c.cost() + t.cost() + f.cost(),
            Sketch::Rec(_, args) => 5 + args.iter().map(SynthCostFunc::cost).sum::<usize>(),
        }
    }
}
/*
impl<T: TypeSystemBounds> PartialOrd for Sketch<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(match (self, other) {
            // Handle equal cases first
            (Sketch::Hole(_), Sketch::Hole(_)) => Ordering::Equal,

            (Sketch::Constant(_), Sketch::Constant(_))
            | (Sketch::Variable(..), Sketch::Variable(..)) => {
                (TryInto::<ProgramNode<T>>::try_into(self).unwrap())
                    .partial_cmp(&other.try_into().unwrap())?
            }

            // Equal program nodes, but maybe not equal sketches
            (Sketch::Operation(_, args1), Sketch::Operation(_, args2))
            | (Sketch::Rec(_, args1), Sketch::Rec(_, args2)) => {
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
            (Sketch::Operation(..), _) => Ordering::Less,
            (_, Sketch::Operation(..)) => Ordering::Greater,

            // Prioritise Rec over Iff
            (Sketch::Rec(..), Sketch::If(..)) => Ordering::Less,
            (Sketch::If(..), Sketch::Rec(..)) => Ordering::Greater,
        })
    }
}

impl<T: TypeSystemBounds> Ord for Sketch<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
} */

/// Information relating to a hole in a sketch
/// There can be more than one hole in a sketch, this is just the information to one of them
/// Each hole data must be unqiue
#[derive(Clone, Debug)]
pub struct HoleMetaData<T: TypeSystemBounds> {
    /// The path threw the sketch to get to this hole
    path: Vec<u8>,
    /// The corresponding nodeid in the ECTA
    nodeid: ECTANode,
    /// Any input/output examples the hole should follow
    pub examples: Examples,
    /// The type of the hole
    typ: T,
    /// How many if statements that one needs to go through to get to this hole
    /// If number is >= `IF_DEPTH` then we can't synthesize an if statement for this hole
    if_depth: usize,
    /// Whether or not there can be a recursive call in this hole
    recursion_allowed: bool,
    /// Whether or not the hole's type should be trusted in synthesizing something
    well_typed: bool,
}

impl<T: TypeSystemBounds> SynthCostFunc for HoleMetaData<T> {
    fn cost(&self) -> usize {
        if self.path.is_empty() {
            0
        } else {
            *self.path.last().unwrap() as usize * self.path.len()
        }
    }
}

impl<T: TypeSystemBounds> HoleMetaData<T> {
    fn new(nodeid: ECTANode, examples: Examples, ty: T, well_typed: bool) -> Self {
        HoleMetaData {
            path: Vec::new(),
            nodeid,
            examples,
            typ: ty,
            if_depth: 0,
            recursion_allowed: false,
            well_typed,
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

    // For creating a hole of the false branch
    fn set_false_hole(self) -> Self {
        Self {
            path: vec![2],
            ..self
        }
    }

    fn get_nodeid(&self) -> ECTANode {
        self.nodeid
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
            .sorted_by_key(|e| e.data.clone())
            .group_by(|edge| edge.data.clone())
            .into_iter()
            .map(|(k, v)| {
                (
                    k,
                    v.into_iter()
                        .sorted_by_key(|p| p.edge_num)
                        .map(|e| e.nodeidx)
                        .collect_vec(),
                )
            })
            .collect();

        let res = iterable
            .into_iter()
            .flat_map(|(p_node, edges)| match p_node {
                LinearProgramNode::Constant(c) => vec![SketchWithData::from_constant(c)],
                LinearProgramNode::Variable(v) => vec![SketchWithData::from_variable(v)],
                LinearProgramNode::Operation(o) => {
                    SketchWithData::from_operation(o, edges, self, state.inverse_map, false)
                }
            })
            .collect_vec();
        res.iter()
            .for_each(|s| s.assert_valid_state(state.ecta, self.nodeid));
        res
    }

    fn deductive_synthesis(&self, state: &SynthesizerState<T>) -> Vec<SketchWithData<T>> {
        /* info!("Attempting deductive synthesis"); */

        let res = state
            .type_map
            .get_all_subtypes(&self.typ)
            .into_iter()
            .flat_map(|o| {
                let lin_o = LinearProgramNode::Operation(o.clone());
                let edges = lin_o
                    .ecta_next_program_nodes(state.ecta, self.nodeid)
                    .unwrap_or_else(|| {
                        (0..o.sig.input.len() + 1)
                            .map(|_| state.ecta.empty_node)
                            .collect()
                    });
                SketchWithData::from_operation(
                    lin_o.try_into().unwrap(),
                    edges,
                    self,
                    state.inverse_map,
                    true,
                )
            })
            .collect_vec();

        // todo: create if statements

        /* info!("Deductive synthesis produced {} sketches", res.len()); */

        res
    }
}

/// Sketches with their corresponding hole data
#[derive(Clone, Debug)]
pub struct SketchWithData<T: TypeSystemBounds> {
    sketch: Sketch<T>,
    holes: MinHeap<HoleMetaData<T>>,
}

impl<T: TypeSystemBounds> Display for SketchWithData<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "{}: {}",
            self.sketch,
            self.holes
                .clone()
                .into_iter()
                .map(|h: HoleMetaData<_>| format!(
                    "\n\t{}\n\t{:?}",
                    h.examples.get_positive_examples().iter().join(", "),
                    h.examples.get_negative_examples().iter().join(", ")
                ))
                .join(", ")
        )
    }
}

impl<T: TypeSystemBounds> SynthCostFunc for SketchWithData<T> {
    fn cost(&self) -> usize {
        self.sketch.cost()
    }
}

impl<T: TypeSystemBounds> TryFrom<SketchWithData<T>> for Program<T> {
    type Error = ();

    fn try_from(value: SketchWithData<T>) -> Result<Self, Self::Error> {
        value.sketch.try_into()
    }
}

impl<T: TypeSystemBounds> From<LinearProgram<T>> for SketchWithData<T> {
    fn from(value: LinearProgram<T>) -> Self {
        SketchWithData {
            sketch: Program::from(value).into(),
            holes: MinHeap::new(),
        }
    }
}

impl<T: TypeSystemBounds> From<Fragment<T>> for SketchWithData<T> {
    fn from(value: Fragment<T>) -> Self {
        SketchWithData {
            sketch: value.into(),
            holes: MinHeap::new(),
        }
    }
}

impl<'a, T: TypeSystemBounds + 'a> SketchWithData<T> {
    pub fn from_hole(ty: T, nodeid: ECTANode, examples: Examples, well_typed: bool) -> Self {
        let mut holes = MinHeap::new();
        holes.push(HoleMetaData::new(nodeid, examples, ty.clone(), well_typed));
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

    pub fn from_variable(v: Variable<T>) -> Self {
        Self {
            sketch: Sketch::Variable(v),
            holes: MinHeap::new(),
        }
    }

    pub fn from_operation(
        o: Operation<T>,
        edges: Vec<ECTANode>,
        holedata: &HoleMetaData<T>,
        inverse_map: &InverseMap<T>,
        from_deductive: bool, // This boolean flag means that we will turn off some assertsions that are not true for deductive synthesis like checking for edges... If they are there, great, but not the end of the world
    ) -> Vec<Self> {
        if o.sig.input.is_empty() {
            /* info!("No arguments in this sketch"); */
            return vec![Self {
                sketch: Sketch::Operation(o.clone(), Vec::new()),
                holes: MinHeap::new(),
            }];
        }

        let args: Vec<_> = o
            .sig
            .input
            .iter()
            .map(|t| Sketch::Hole(t.clone()))
            .collect();

        let examples_vec: Option<Vec<Vec<Examples>>> = holedata
            .examples
            .propogate_operation_examples(&o, inverse_map);
        /* holedata.examples.witness_examples(&o, inverse_map); */

        if examples_vec.is_none() {
            /* info!("Examples_vec is none"); */
            return Vec::new();
        }

        let examples_vec = examples_vec.unwrap();

        assert!(!examples_vec.iter().any(|v| v.is_empty()));

        // We skip one on the edges because the first edge has to do with the node type
        assert!(edges.len() == o.sig.input.len() + 1);
        assert!(args.len() == o.sig.input.len());

        examples_vec
            .into_iter()
            .map(|examples_v| {
                let holes: MinHeap<_> = o
                    .sig
                    .input
                    .iter()
                    .enumerate()
                    .zip(examples_v)
                    .zip(edges.iter().skip(1))
                    .map(|(((idx, t), examples), nodeidx)| HoleMetaData {
                        path: vec![idx as u8],
                        examples,
                        nodeid: *nodeidx,
                        typ: t.clone(),
                        if_depth: holedata.if_depth,
                        recursion_allowed: holedata.recursion_allowed,
                        well_typed: holedata.well_typed && o.sig.output.is_subtype(&holedata.typ),
                    })
                    .collect();
                assert!(!holes.is_empty());
                assert!(args.len() == holes.len());
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
        path: Vec<u8>,
        is_recursable: bool,
    ) -> impl Fn(SketchWithData<T>) -> SketchWithData<T> + 'a {
        move |x| -> SketchWithData<T> {
            let path = path.clone();
            let sketch = self.sketch.clone();
            let other_holes = self.holes.clone();
            fn helper<T: TypeSystemBounds>(
                x: SketchWithData<T>,
                mut path: Vec<u8>,
                sketch: Sketch<T>,
                is_recursable: bool,
            ) -> SketchWithData<T> {
                if path.is_empty() {
                    assert!(matches!(sketch, Sketch::Hole(_)));
                    x
                } else {
                    let i = path.pop().unwrap();
                    match sketch {
                        Sketch::Hole(_) | Sketch::Constant(_) | Sketch::Variable(..) => panic!(),
                        Sketch::Operation(o, mut args) => {
                            let SketchWithData { sketch, holes } =
                                helper(x, path, args[i as usize].clone(), is_recursable);
                            args[i as usize] = sketch;

                            let holes = holes.into_iter().map(|h| h.add_depth(i)).collect();

                            SketchWithData {
                                sketch: Sketch::Operation(o, args),
                                holes,
                            }
                        }
                        Sketch::Rec(t, mut args) => {
                            let SketchWithData { sketch, holes } =
                                helper(x, path, args[i as usize].clone(), is_recursable);
                            args[i as usize] = sketch;

                            let holes = holes.into_iter().map(|h| h.add_depth(i)).collect();

                            SketchWithData {
                                sketch: Sketch::Rec(t, args),
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
                                    let SketchWithData { sketch, holes } =
                                        helper(x, path, *t1, is_recursable);
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
                                    let SketchWithData { sketch, holes } =
                                        helper(x, path, *f1, is_recursable);
                                    *f1 = sketch;
                                    (
                                        holes
                                            .into_iter()
                                            .map(|h: HoleMetaData<_>| {
                                                let tmp = h.add_depth(2).inc_if();
                                                if is_recursable {
                                                    tmp.allow_recursion()
                                                } else {
                                                    tmp
                                                }
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
            let mut x = helper(x, path, sketch, is_recursable);
            x.holes.extend(other_holes);
            x
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
            .filter_map(|b| {
                // Rule out any conditions that don't evaluate correctly on a test case
                if !holedata
                    .examples
                    .is_consistent_with(|t| b.fragment.interpret(&t.into()).is_ok())
                {
                    return None;
                }

                // The sketch on then left branch might be complete
                // In which case it is fine that it didn't have any holes
                let true_holes = if self.holes.is_empty() {
                    Vec::new()
                } else {
                    let true_holes: Vec<_> = self
                        .holes
                        .clone()
                        .into_iter()
                        .map(|h| h.add_depth(1).inc_if())
                        .filter_map(|mut hmd| {
                            let new_e = hmd
                                .examples
                                .filter_behavior(&b.fragment, |c| c == &Constant::Bool(true));
                            if new_e.get_positive_examples().is_empty() {
                                None
                            } else {
                                hmd.examples = new_e;
                                Some(hmd)
                            }
                        })
                        .collect();

                    if true_holes.is_empty() {
                        /* info!("Ruled out sketch because no examples for true branch"); */
                        return None;
                    }
                    true_holes
                };

                let mut false_hole = holedata.clone().set_false_hole().inc_if();

                false_hole = if state.sig.is_recursable() {
                    false_hole.allow_recursion()
                } else {
                    false_hole
                };

                false_hole.examples = false_hole
                    .examples
                    .filter_behavior(&b.fragment, |c| c == &Constant::Bool(false));

                if false_hole.examples.get_positive_examples().is_empty() {
                    /* info!("Ruled out sketch because no examples for false branch"); */
                    return None;
                }

                let holes: MinHeap<_> = true_holes.into_iter().chain(once(false_hole)).collect();
                assert!(!holes.is_empty());

                Some(Self {
                    sketch: Sketch::If(
                        Box::new(b.fragment.clone().into()),
                        Box::new(self.sketch.clone()),
                        Box::new(Sketch::Hole(holedata.typ.clone())),
                    ),
                    holes,
                })
            })
            .collect()
    }

    pub fn fill_hole(mut self, state: &SynthesizerState<T>, examples: &Examples) -> Vec<Self> {
        assert!(!self.is_complete());
        // What do you need to fill a sketch?
        // Where is the hole?
        // What can I fill it with?
        // Sketch has a spine to the location of the hole
        // Sketch has a node in the ecta

        self.assert_valid_state(state.ecta, state.start_node);

        let holedata = self.holes.pop().unwrap();
        /* info!("Current holedata: {holedata:?}"); */

        // walk to the hole,
        // then construct new ones with the hole filled(possibly with new holes)
        let f = self
            .clone()
            .sketch_constructor(holedata.path.clone(), state.sig.is_recursable());

        // Check if we already have a solution for this hole from the traces
        if let Some(frag) = state
            .fragment_collection
            .find_complete_trace(&holedata.examples)
            .into_iter()
            .map(|f| f.fragment.clone())
            .filter(|p| p.is_trace_consistent(state.ecta, holedata.nodeid))
            .collect::<MinHeap<LinearProgram<T>>>()
            .pop()
        {
            /* info!("Found complete fragment for hole: {frag}"); */
            return vec![f(frag.into())];
        }

        // Get possible candidates from the ecta
        let mut candidates = holedata.get_edge_candidates(state);

        // Todo what is this doing again?
        candidates.iter().for_each(|s| {
            if s.is_complete() {
                let _: Program<T> = s.sketch.clone().try_into().unwrap();
            }
        });

        let mut deductive_candidates = Vec::new();

        if holedata.well_typed {
            deductive_candidates.extend(holedata.deductive_synthesis(state));
        }

        if deductive_candidates.is_empty() {
            /* info!("No deductive candidates to fill hole"); */
        } else {
            info!(
                "Deductive hole filling candidates: \n{}",
                deductive_candidates
                    .iter()
                    .map(ToString::to_string)
                    .collect_vec()
                    .join("")
            );
        }

        if candidates.is_empty() {
            info!("No inductive candidates to fill hole of {self}");
            return deductive_candidates;
        }

        /*         info!(
            "Hole filling candidates: \n{}",
            candidates
                .iter()
                .map(ToString::to_string)
                .collect_vec()
                .join("")
        ); */

        /* #[cfg(debug_assertions)] */
        candidates
            .iter()
            .for_each(|s| s.assert_valid_state(state.ecta, holedata.nodeid));

        candidates = if holedata.if_depth < IF_DEPTH {
            candidates.into_iter().fold(Vec::new(), |mut acc, x| {
                acc.extend(x.create_if_sketch(state, &holedata));
                acc.push(x);
                acc
            })
        } else {
            candidates
        };

        if holedata.recursion_allowed {
            candidates.extend(SketchWithData::create_rec_sketch(state, &holedata))
        }

        info!(
            "Hole filling candidates with control flow: \n{}",
            candidates.len() /*                 .iter()
                             .map(ToString::to_string)
                             .collect_vec()
                             .join("") */
        );

        /* #[cfg(debug_assertions)] */
        candidates
            .iter()
            .for_each(|s| s.assert_valid_state(state.ecta, holedata.nodeid));

        /* info!("Examples: {}", holedata.examples); */

        let mut sketches: Vec<_> = candidates
            .into_iter()
            .map(&f)
            .filter(|s| {
                s.sketch.symbolic_block_based_evaluator(
                    examples,
                    state,
                    state.start_node,
                    &s.sketch,
                )
            })
            .collect();

        sketches.extend(deductive_candidates.into_iter().map(f));

        info!(
            "New sketches with control flow: \n{}",
            sketches.len() /* .iter()
                           .map(ToString::to_string)
                           .collect_vec()
                           .join("") */
        );

        /* #[cfg(debug_assertions)] */
        sketches
            .iter()
            .for_each(|s| s.assert_valid_state(state.ecta, state.start_node));

        sketches
    }

    pub fn is_complete(&self) -> bool {
        self.holes.is_empty()
    }

    // Lets actually not synthesize a recursive sketch with holes
    // That just makes things more tricky if we can avoid it
    // We can just stick in blocks for each value from the bottom up enumeration
    pub fn create_rec_sketch(state: &SynthesizerState<T>, holedata: &HoleMetaData<T>) -> Vec<Self> {
        /* info!("Creating a recursive sketch"); */
        let sig = state.sig;
        assert!(sig.output.is_closed());
        let typ = sig.output.clone();

        /* warn!("TODO: Should I be doing something with the holedata?"); */

        // First argument should not be a hole but instead an observably smaller value
        // So we skip the first value and put something concrete instead
        assert!(sig.input.len() > 0); // Otherwise it shouldn't be recursible

        // Want to iterate through the list of signature inputs
        // And pass to the recursive function the first argument as a strictly smaller version of the original input
        assert!(!state.sig.input[0].is_non_trivial()); // The next piece of code blows up without simple equalities
        let possible_arg_one = state
            .fragment_collection
            .get_recursable_blocks(&state.sig.input[0]);
        // And the rest as small blocks for arguments that are consistent with the examples if they exist
        let other_args = state.sig.input.iter().skip(1).map(|ty| {
            state
                .fragment_collection
                .get_small_traces(ty, 2.try_into().unwrap())
        });

        once(possible_arg_one)
            .chain(other_args)
            .multi_cartesian_product()
            .map(|args| SketchWithData {
                sketch: Sketch::Rec(typ.clone(), args.into_iter().map(|f| f.into()).collect()),
                holes: MinHeap::new(),
            })
            .collect()
    }

    /// For checking if all the holes are valid
    pub fn assert_valid_state(&self, ecta: &SynthEcta<T>, start_node: ECTANode) {
        let SketchWithData { sketch, mut holes } = self.clone();
        match sketch {
            Sketch::Hole(_) => {
                assert!(holes.len() == 1);
                let HoleMetaData {
                    path,
                    nodeid,
                    well_typed,
                    ..
                } = holes.pop().unwrap();
                assert!(path.is_empty());

                if !well_typed {
                    assert!(nodeid != ecta.empty_node);
                    assert!(nodeid == start_node);
                }
            }
            Sketch::Constant(c) => {
                assert!(holes.is_empty());

                assert!(LinearProgramNode::Constant(c)
                    .ecta_next_program_nodes(ecta, start_node)
                    .is_some())
            }
            Sketch::Variable(v) => {
                assert!(holes.is_empty());
                assert!(LinearProgramNode::Variable(v)
                    .ecta_next_program_nodes(ecta, start_node)
                    .is_some())
            }
            Sketch::If(_, t, f) => {
                let (holes1, holes2) = holes.into_iter().fold(
                    (MinHeap::new(), MinHeap::new()),
                    |(mut holes1, mut holes2), h| {
                        let HoleMetaData {
                            mut path,
                            if_depth,
                            recursion_allowed,
                            ..
                        } = h;
                        assert!(if_depth > 0);

                        let dir = path.pop().unwrap();

                        assert!(dir == 1 || dir == 2);

                        let hole = HoleMetaData { path, ..h };
                        if dir == 1 {
                            if if_depth == 1 {
                                // Simple check, doesn't get all cases where recursion isn't allowed
                                assert!(!recursion_allowed);
                            }
                            holes1.push(hole);
                        } else {
                            holes2.push(hole);
                        }
                        (holes1, holes2)
                    },
                );

                SketchWithData {
                    sketch: *t,
                    holes: holes1,
                }
                .assert_valid_state(ecta, start_node);

                SketchWithData {
                    sketch: *f,
                    holes: holes2,
                }
                .assert_valid_state(ecta, start_node)
            }

            Sketch::Rec(_, args) => {
                assert!(args.len() > 0);

                args.iter()
                    .for_each(|a| assert!(!matches!(a, Sketch::Hole(_))));
            }
            Sketch::Operation(o, args) => {
                let init_heaps = (0..args.len()).map(|_| MinHeap::new()).collect_vec();

                // Every arguent to the operation has some number of holes
                // Those holes are stored in a min heap
                let argument_holes: Vec<_> = holes.into_iter().fold(init_heaps, |mut acc, h| {
                    let HoleMetaData { mut path, .. } = h;

                    let dir = path.pop().unwrap();

                    acc[dir as usize].push(HoleMetaData { path, ..h });

                    acc
                });

                let edge_nodes = LinearProgramNode::Operation(o)
                    .ecta_next_program_nodes(ecta, start_node)
                    .unwrap();

                assert!(argument_holes.len() == args.len());

                argument_holes
                    .into_iter()
                    .zip(args.into_iter().enumerate())
                    .for_each(|(holes, (idx, arg))| {
                        SketchWithData {
                            sketch: arg,
                            holes,
                        }
                        // Plus one because the first node is the return type
                        .assert_valid_state(ecta, edge_nodes[idx])
                    })
            }
        }
    }
}
