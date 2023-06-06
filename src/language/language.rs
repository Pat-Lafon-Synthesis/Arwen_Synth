use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::rc::Rc;

use ecta_rs::{ECTANode, Edge};
use itertools::Itertools;

use crate::data_structures::SynthCostFunc;
use crate::types::{Signature, TypeSystemBounds};
use crate::{SynthEcta, SynthEctaEdge};

use super::TestCase;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Tree<T: Display> {
    Leaf,
    Node(T, Box<Tree<T>>, Box<Tree<T>>),
}

impl<T: Display> Display for Tree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Tree::Leaf => "leaf".to_string(),
                Tree::Node(n, t1, t2) => format!("node {} ({}) ({})", n, t1, t2),
            }
        )
    }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum Constant {
    Int(i64),
    Bool(bool),
    IntList(Vec<i64>),
    IntTree(Tree<i64>),
}

impl Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Constant::Int(i) => i.to_string(),
                Constant::Bool(b) => b.to_string(),
                Constant::IntList(l) => format!("[{}]", l.iter().rev().join(", ")),
                Constant::IntTree(_) => "tree".to_string(),
            }
        )
    }
}

impl From<i64> for Constant {
    fn from(i: i64) -> Self {
        Constant::Int(i)
    }
}

impl TryFrom<Constant> for i64 {
    type Error = InvalidProg;

    fn try_from(value: Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::Int(i) => Ok(i),
            _ => Err(InvalidProg {}),
        }
    }
}

impl TryFrom<&Constant> for i64 {
    type Error = InvalidProg;

    fn try_from(value: &Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::Int(i) => Ok(*i),
            _ => Err(InvalidProg {}),
        }
    }
}

impl From<bool> for Constant {
    fn from(b: bool) -> Self {
        Constant::Bool(b)
    }
}

impl TryFrom<Constant> for bool {
    type Error = InvalidProg;

    fn try_from(value: Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::Bool(b) => Ok(b),
            _ => Err(InvalidProg {}),
        }
    }
}

impl TryFrom<&Constant> for bool {
    type Error = InvalidProg;

    fn try_from(value: &Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::Bool(b) => Ok(*b),
            _ => Err(InvalidProg {}),
        }
    }
}

impl From<Vec<i64>> for Constant {
    fn from(v: Vec<i64>) -> Self {
        Constant::IntList(v)
    }
}

impl TryFrom<Constant> for Vec<i64> {
    type Error = InvalidProg;

    fn try_from(value: Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::IntList(v) => Ok(v),
            _ => Err(InvalidProg {}),
        }
    }
}

impl From<Tree<i64>> for Constant {
    fn from(t: Tree<i64>) -> Self {
        Constant::IntTree(t)
    }
}

impl TryFrom<Constant> for Tree<i64> {
    type Error = InvalidProg;

    fn try_from(value: Constant) -> Result<Self, Self::Error> {
        match value {
            Constant::IntTree(t) => Ok(t),
            _ => Err(InvalidProg {}),
        }
    }
}

pub type SynthFuncType = dyn Fn(&Vec<Constant>) -> Result<Constant, InvalidProg>;

#[derive(Clone)]
pub struct Operation<T> {
    pub name: String,
    pub sig: Signature<T>,
    pub code: Rc<SynthFuncType>,
}

impl<T> Operation<T> {
    pub fn execute(&self, args: &Vec<Constant>) -> Result<Constant, InvalidProg> {
        (self.code)(args)
    }
}

impl<T> Display for Operation<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl<T: Debug> std::fmt::Debug for Operation<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Operation")
            .field("name", &self.name)
            .field("sig", &self.sig)
            .finish()
    }
}

impl<T> Hash for Operation<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl<T> PartialEq for Operation<T> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl<T> Eq for Operation<T> {}

impl<T> PartialOrd for Operation<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.name.partial_cmp(&other.name)
    }
}

impl<T> Ord for Operation<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Variable<T: TypeSystemBounds> {
    pub name: String,
    pub ty: T,
}

impl<T: TypeSystemBounds> Display for Variable<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

// Program node that can be used to create a block/trace
// Basically no if statements or recursive calls
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LinearProgramNode<T: TypeSystemBounds> {
    Constant(Constant),
    Variable(Variable<T>),
    Operation(Operation<T>),
}

impl<T: TypeSystemBounds> LinearProgramNode<T> {
    /// Produces a sorted list of next nodes for a given edge
    pub fn ecta_next_program_nodes(
        &self,
        ecta: &SynthEcta<T>,
        start_node: ECTANode,
    ) -> Option<Vec<ECTANode>> {
        self.ecta_next_edges(ecta, start_node).map(|edges| {
            edges
                .into_iter()
                .sorted_by_key(|e| e.edge_num)
                // Skipping the edge that is the return type
                .skip(1)
                .map(|e| e.nodeidx)
                .collect_vec()
        })
    }

    fn ecta_next_edges(
        &self,
        ecta: &SynthEcta<T>,
        start_node: ECTANode,
    ) -> Option<Vec<Edge<SynthEctaEdge<T>, ()>>> {
        // Get the group of edges for this operation
        let g_group = ecta
            .get_edges(start_node)
            .sorted_by_key(|e| e.data.clone())
            .group_by(|e| e.data.clone());

        let g = g_group.into_iter();

        let mut edge_nodes = g
            .filter(|e| matches!(&e.0, SynthEctaEdge::P(o2) if self == o2))
            .collect_vec();

        if edge_nodes.is_empty() {
            return None;
        }

        // Check that there was only one option
        assert!(edge_nodes.len() == 1);

        // All the edges for the operation in the ecta
        let x = Some(edge_nodes.pop().unwrap().1.cloned().collect_vec());
        x
    }
}

impl<T: TypeSystemBounds> Display for LinearProgramNode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinearProgramNode::Constant(c) => write!(f, "{c}"),
            LinearProgramNode::Variable(v) => write!(f, "{v}"),
            LinearProgramNode::Operation(o) => write!(f, "{}", o),
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<LinearProgramNode<T>> for Operation<T> {
    type Error = ();

    fn try_from(value: LinearProgramNode<T>) -> Result<Self, Self::Error> {
        match value {
            LinearProgramNode::Constant(_) => Err(()),
            LinearProgramNode::Variable(_) => Err(()),
            LinearProgramNode::Operation(o) => Ok(o),
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<LinearProgramNode<T>> for Variable<T> {
    type Error = ();

    fn try_from(value: LinearProgramNode<T>) -> Result<Self, Self::Error> {
        match value {
            LinearProgramNode::Constant(_) => Err(()),
            LinearProgramNode::Variable(v) => Ok(v),
            LinearProgramNode::Operation(_) => Err(()),
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<LinearProgramNode<T>> for Constant {
    type Error = ();

    fn try_from(value: LinearProgramNode<T>) -> Result<Self, Self::Error> {
        match value {
            LinearProgramNode::Constant(c) => Ok(c),
            LinearProgramNode::Variable(_) => Err(()),
            LinearProgramNode::Operation(_) => Err(()),
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<ProgramNode<T>> for LinearProgramNode<T> {
    type Error = ();

    fn try_from(value: ProgramNode<T>) -> Result<Self, ()> {
        match value {
            ProgramNode::Constant(c) => Ok(LinearProgramNode::Constant(c)),
            ProgramNode::Variable(v) => Ok(LinearProgramNode::Variable(v)),
            ProgramNode::Operation(o) => Ok(LinearProgramNode::Operation(o)),
            ProgramNode::If => Err(()),
            ProgramNode::Rec(_) => Err(()),
        }
    }
}

impl<T: TypeSystemBounds> From<LinearProgramNode<T>> for ProgramNode<T> {
    fn from(value: LinearProgramNode<T>) -> Self {
        match value {
            LinearProgramNode::Constant(c) => ProgramNode::Constant(c),
            LinearProgramNode::Variable(v) => ProgramNode::Variable(v),
            LinearProgramNode::Operation(o) => ProgramNode::Operation(o),
        }
    }
}

#[derive(Debug, Clone)]
pub struct LinearProgram<T: TypeSystemBounds> {
    pub node: LinearProgramNode<T>,
    pub args: Vec<LinearProgram<T>>,
}

impl<T: TypeSystemBounds> LinearProgram<T> {
    pub fn new(node: LinearProgramNode<T>, args: Vec<LinearProgram<T>>) -> Self {
        Self { node, args }
    }

    pub fn is_trace_consistent(&self, ecta: &SynthEcta<T>, start_node: ECTANode) -> bool {
        if let Some(nodes) = self.node.ecta_next_program_nodes(ecta, start_node) {
            assert!(nodes.len() == self.args.len());
            self.args
                .iter()
                .zip(nodes.iter())
                .all(|(a, n)| a.is_trace_consistent(ecta, *n))
        } else {
            false
        }
    }
    pub fn contains_variable(&self) -> bool {
        match self.node {
            LinearProgramNode::Variable(_) => true,
            LinearProgramNode::Constant(_) => false,
            LinearProgramNode::Operation(_) => self.args.iter().any(|a| a.contains_variable()),
        }
    }

    pub fn interpret(&self, e: &Environment<T>) -> Result<Constant, InvalidProg> {
        let LinearProgram { node, args } = self;
        Ok(match node {
            LinearProgramNode::Constant(c) => c.clone(),
            LinearProgramNode::Variable(v) => e.get(v).unwrap().clone(),
            LinearProgramNode::Operation(o) => {
                let args = args.iter().map(|a| a.interpret(e)).try_collect()?;
                o.execute(&args)?
            }
        })
    }

    pub fn get_behavior(&self, tests: &[TestCase]) -> Vec<TestCase> {
        tests
            .iter()
            .filter_map(|t| {
                self.interpret(&t.into()).ok().map(|output| TestCase {
                    inputs: t.inputs.clone(),
                    output,
                })
            })
            .collect()
    }

    pub fn get_type(&self) -> T {
        match &self.node {
            LinearProgramNode::Constant(c) => c.clone().into(),
            LinearProgramNode::Variable(v) => v.ty.clone(),
            LinearProgramNode::Operation(o) => o.sig.output.clone(),
        }
    }
}

impl<T: TypeSystemBounds> Display for LinearProgram<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", Program::from(self.clone()))
    }
}

impl<T: TypeSystemBounds> SynthCostFunc for LinearProgram<T> {
    fn cost(&self) -> usize {
        match &self.node {
            LinearProgramNode::Variable(_) => 1,
            LinearProgramNode::Constant(_) => 2,
            LinearProgramNode::Operation(_) => {
                3 + self.args.iter().map(|a| a.cost()).sum::<usize>()
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProgramNode<T: TypeSystemBounds> {
    Constant(Constant),
    Variable(Variable<T>),
    Operation(Operation<T>),
    If,
    Rec(T), // Recursive Call
}

impl<T: TypeSystemBounds> Display for ProgramNode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProgramNode::Constant(c) => write!(f, "{c}"),
            ProgramNode::Variable(v) => write!(f, "{v}"),
            ProgramNode::Operation(o) => write!(f, "{}", o),
            ProgramNode::If => write!(f, "if"),
            ProgramNode::Rec(t) => write!(f, "rec<{t}>"),
        }
    }
}

pub struct Environment<T: TypeSystemBounds>(HashMap<Variable<T>, Constant>);

impl<T: TypeSystemBounds> Environment<T> {
    pub fn new() -> Self {
        Environment(HashMap::new())
    }

    pub fn get(&self, v: &Variable<T>) -> Option<&Constant> {
        self.0.get(v)
    }
}

impl<T: TypeSystemBounds> Default for Environment<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: TypeSystemBounds> From<&TestCase> for Environment<T> {
    fn from(TestCase { inputs, .. }: &TestCase) -> Self {
        Environment(
            inputs
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    (
                        Variable {
                            name: format!("arg{i:?}"),
                            ty: Into::<T>::into(c.clone()),
                        },
                        c.clone(),
                    )
                })
                .collect(),
        )
    }
}

impl<T: TypeSystemBounds> From<&Vec<Constant>> for Environment<T> {
    fn from(inputs: &Vec<Constant>) -> Self {
        Environment(
            inputs
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    (
                        Variable {
                            name: format!("arg{i:?}"),
                            ty: Into::<T>::into(c.clone()),
                        },
                        c.clone(),
                    )
                })
                .collect(),
        )
    }
}

impl<T: TypeSystemBounds> From<Vec<Constant>> for Environment<T> {
    fn from(inputs: Vec<Constant>) -> Self {
        Environment(
            inputs
                .into_iter()
                .enumerate()
                .map(|(i, c)| {
                    (
                        Variable {
                            name: format!("arg{i:?}"),
                            ty: Into::<T>::into(c.clone()),
                        },
                        c,
                    )
                })
                .collect(),
        )
    }
}

#[derive(Debug)]
pub struct InvalidProg {}

#[derive(Debug, Clone /* , PartialEq, Eq */)]
pub struct Program<T: TypeSystemBounds> {
    pub node: ProgramNode<T>,
    pub args: Vec<Program<T>>,
}

impl<T: TypeSystemBounds> Program<T> {
    pub fn new(node: ProgramNode<T>, args: Vec<Program<T>>) -> Self {
        Program { node, args }
    }

    pub fn interpret(
        &self,
        e: &Environment<T>,
        full_program: &Self,
    ) -> Result<Constant, InvalidProg> {
        let Program { node, args } = self;
        Ok(match node {
            ProgramNode::Constant(c) => c.clone(),
            ProgramNode::Variable(v) => e.get(v).unwrap().clone(),
            ProgramNode::Operation(o) => {
                let args = args
                    .iter()
                    .map(|a| a.interpret(e, full_program))
                    .try_collect()?;
                o.execute(&args)?
            }
            ProgramNode::Rec(_) => {
                let args: Vec<Constant> = args
                    .iter()
                    .map(|a| a.interpret(e, full_program))
                    .try_collect()?;

                let new_e = &(&args).into();

                full_program.interpret(new_e, full_program)?
            }
            ProgramNode::If => {
                if args.get(0).unwrap().interpret(e, full_program)? == Constant::Bool(true) {
                    args.get(1).unwrap().interpret(e, full_program)?
                } else {
                    args.get(2).unwrap().interpret(e, full_program)?
                }
            }
        })
    }

    pub fn get_behavior(&self, tests: &[TestCase]) -> Vec<TestCase> {
        tests
            .iter()
            .filter_map(|t| {
                self.interpret(&t.into(), self).ok().map(|output| TestCase {
                    inputs: t.inputs.clone(),
                    output,
                })
            })
            .collect()
    }

    pub fn passes_test_case(&self, t: &TestCase) -> bool {
        self.interpret(&t.into(), self)
            .map_or(false, |output| output == t.output)
    }

    pub fn passes_all_test_cases(&self, v: &[TestCase]) -> bool {
        v.iter().all(|t| self.passes_test_case(t))
    }

    pub fn get_type(&self) -> T {
        match &self.node {
            ProgramNode::Constant(c) => c.clone().into(),
            ProgramNode::Variable(v) => v.ty.clone(),
            ProgramNode::Operation(o) => o.sig.output.clone(),
            ProgramNode::If => self.args.get(1).unwrap().get_type(),
            ProgramNode::Rec(t) => t.clone(),
        }
    }
}

impl<T: TypeSystemBounds> From<LinearProgram<T>> for Program<T> {
    fn from(LinearProgram { node, args }: LinearProgram<T>) -> Self {
        Program {
            node: node.into(),
            args: args.into_iter().map(|a| a.into()).collect(),
        }
    }
}

impl<T: TypeSystemBounds> SynthCostFunc for Program<T> {
    fn cost(&self) -> usize {
        match &self.node {
            ProgramNode::Variable(_) => 1,
            ProgramNode::Constant(_) => 2,
            ProgramNode::Operation(_) => 3 + self.args.iter().map(|a| a.cost()).sum::<usize>(),
            ProgramNode::If => 4 + self.args.iter().map(|a| a.cost()).sum::<usize>(),
            ProgramNode::Rec(_) => 5 + self.args.iter().map(|a| a.cost()).sum::<usize>(),
        }
    }
}

impl<T: TypeSystemBounds> Display for Program<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.node {
            ProgramNode::Constant(c) => write!(f, "{c}"),
            ProgramNode::Variable(v) => write!(f, "{v}"),
            ProgramNode::Operation(o) => write!(
                f,
                "{o}({})",
                self.args.iter().map(ToString::to_string).join(",")
            ),
            ProgramNode::Rec(t) => write!(
                f,
                "rec<{t}>({})",
                self.args.iter().map(ToString::to_string).join(",")
            ),
            ProgramNode::If => write!(
                f,
                "if ({}) {{{}}} else {{{}}}",
                self.args.get(0).unwrap(),
                self.args.get(1).unwrap(),
                self.args.get(2).unwrap()
            ),
        }
    }
}
