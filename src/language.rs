use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::rc::Rc;

use itertools::Itertools;

use crate::types::{BaseType, RefinementType, Signature, TypeSystemBounds};

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
                Constant::IntList(_) => "list".to_string(),
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

impl From<bool> for Constant {
    fn from(b: bool) -> Self {
        Constant::Bool(b)
    }
}

impl From<Vec<i64>> for Constant {
    fn from(v: Vec<i64>) -> Self {
        Constant::IntList(v)
    }
}

impl From<Tree<i64>> for Constant {
    fn from(t: Tree<i64>) -> Self {
        Constant::IntTree(t)
    }
}

#[derive(Clone)]
pub struct Operation<T> {
    pub name: String,
    pub sig: Signature<T>,
    pub code: Rc<dyn Fn(&Vec<Constant>) -> Result<Constant, InvalidProg>>,
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LinearProgramNode<T: TypeSystemBounds> {
    Constant(Constant),
    Variable(Variable<T>, T),
    Operation(Operation<T>),
}

impl<T: TypeSystemBounds> PartialOrd for LinearProgramNode<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (LinearProgramNode::Variable(..), LinearProgramNode::Variable(..)) => {
                Some(Ordering::Equal)
            }
            (LinearProgramNode::Constant(_), LinearProgramNode::Constant(_)) => {
                Some(Ordering::Equal)
            }
            (LinearProgramNode::Operation(_), LinearProgramNode::Operation(_)) => {
                Some(Ordering::Equal)
            }

            (LinearProgramNode::Constant(_), _) => Some(Ordering::Greater),
            (_, LinearProgramNode::Constant(_)) => Some(Ordering::Less),

            (LinearProgramNode::Variable(..), LinearProgramNode::Operation(_)) => {
                Some(Ordering::Less)
            }
            (LinearProgramNode::Operation(_), LinearProgramNode::Variable(..)) => {
                Some(Ordering::Greater)
            }
        }
    }
}

impl<T: TypeSystemBounds> Ord for LinearProgramNode<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<T: TypeSystemBounds> Display for LinearProgramNode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinearProgramNode::Constant(c) => write!(f, "{c}"),
            LinearProgramNode::Variable(v, _) => write!(f, "{v}"),
            LinearProgramNode::Operation(o) => write!(f, "{}", o),
        }
    }
}

impl<T: TypeSystemBounds> TryFrom<ProgramNode<T>> for LinearProgramNode<T> {
    type Error = ();

    fn try_from(value: ProgramNode<T>) -> Result<Self, ()> {
        match value {
            ProgramNode::Constant(c) => Ok(LinearProgramNode::Constant(c)),
            ProgramNode::Variable(v, t) => Ok(LinearProgramNode::Variable(v, t)),
            ProgramNode::Operation(o) => Ok(LinearProgramNode::Operation(o)),
            ProgramNode::If => Err(()),
        }
    }
}

impl<T: TypeSystemBounds> From<LinearProgramNode<T>> for ProgramNode<T> {
    fn from(value: LinearProgramNode<T>) -> Self {
        match value {
            LinearProgramNode::Constant(c) => ProgramNode::Constant(c),
            LinearProgramNode::Variable(v, t) => ProgramNode::Variable(v, t),
            LinearProgramNode::Operation(o) => ProgramNode::Operation(o),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProgramNode<T: TypeSystemBounds> {
    Constant(Constant),
    Variable(Variable<T>, T),
    Operation(Operation<T>),
    If,
}

impl<T: TypeSystemBounds> PartialOrd for ProgramNode<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (ProgramNode::If, ProgramNode::If) => Some(Ordering::Equal),
            (ProgramNode::Variable(..), ProgramNode::Variable(..)) => Some(Ordering::Equal),
            (ProgramNode::Constant(_), ProgramNode::Constant(_)) => Some(Ordering::Equal),
            (ProgramNode::Operation(_), ProgramNode::Operation(_)) => Some(Ordering::Equal),

            (_, ProgramNode::If) => Some(Ordering::Less),
            (ProgramNode::If, _) => Some(Ordering::Greater),
            (ProgramNode::Constant(_), _) => Some(Ordering::Greater),
            (_, ProgramNode::Constant(_)) => Some(Ordering::Less),

            (ProgramNode::Variable(..), ProgramNode::Operation(_)) => Some(Ordering::Less),
            (ProgramNode::Operation(_), ProgramNode::Variable(..)) => Some(Ordering::Greater),
        }
    }
}

impl<T: TypeSystemBounds> Ord for ProgramNode<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<T: TypeSystemBounds> Display for ProgramNode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProgramNode::Constant(c) => write!(f, "{c}"),
            ProgramNode::Variable(v, _) => write!(f, "{v}"),
            ProgramNode::Operation(o) => write!(f, "{}", o),
            ProgramNode::If => write!(f, "if"),
        }
    }
}

type Environment<T> = HashMap<Variable<T>, Constant>;

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct TestCase {
    pub inputs: Vec<Constant>,
    pub output: Constant,
}

impl TestCase {
    fn into_env<T: TypeSystemBounds>(&self) -> Environment<T> {
        let TestCase { inputs, .. } = self;
        inputs
            .iter()
            .enumerate()
            .map(|(i, c)| {
                (
                    Variable {
                        name: format!("arg{i:?}"),
                        ty: Into::<T>::into(c.clone()).into(),
                    },
                    c.clone(),
                )
            })
            .collect()
    }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sketch<T: TypeSystemBounds> {
    Hole(T),
    Constant(Constant),
    Variable(Variable<T>, T),
    Operation(Operation<T>, Vec<Sketch<T>>),
    If(Box<Sketch<T>>, Box<Sketch<T>>, Box<Sketch<T>>),
}

impl From<&Sketch<BaseType>> for BaseType {
    fn from(s: &Sketch<BaseType>) -> Self {
        match s {
            Sketch::Hole(t) => t.clone(),
            Sketch::Constant(c) => c.clone().into(),
            Sketch::Variable(_, t) => t.clone(),
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
                args: vec![(*b).try_into()?, (*s1).try_into()?, (*s2).try_into()?],
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
            (Sketch::Operation(o1, args1), Sketch::Operation(o2, args2)) => {
                assert!(o1 == o2); // Do I need to handle something special when the operations are different? Maybe order operations with fewer arguments first? Maybe choose more specific types first
                if args1.is_empty() && args2.is_empty() {
                    Ordering::Equal
                } else {
                    args1[0].partial_cmp(&args2[0]).unwrap()
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

            // Choose empty hole last
            (Sketch::Hole(_), _) => Ordering::Greater,
            (_, Sketch::Hole(_)) => Ordering::Less,

            // Then choose variables first
            (Sketch::Variable(..), _) => Ordering::Less,
            (_, Sketch::Variable(..)) => Ordering::Greater,

            // Then choose constants to help fail fast?
            (Sketch::Constant(_), _) => Ordering::Less,
            (_, Sketch::Constant(_)) => Ordering::Greater,

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

#[derive(Debug)]
pub struct InvalidProg {}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct Program<T: TypeSystemBounds> {
    pub node: ProgramNode<T>,
    pub args: Vec<Program<T>>,
}

impl<T: TypeSystemBounds> Program<T> {
    pub fn new((node, args): (ProgramNode<T>, Vec<Program<T>>)) -> Self {
        Program { node, args }
    }
}

impl From<&Program<BaseType>> for BaseType {
    fn from(p: &Program<BaseType>) -> Self {
        match &p.node {
            ProgramNode::Constant(c) => c.clone().into(),
            ProgramNode::Variable(_, t) => *t,
            ProgramNode::Operation(o) => o.sig.output,
            ProgramNode::If => p.args.get(1).unwrap().into(),
        }
    }
}

impl From<&Program<RefinementType>> for RefinementType {
    fn from(p: &Program<RefinementType>) -> Self {
        match &p.node {
            ProgramNode::Constant(c) => c.clone().into(),
            ProgramNode::Variable(_, t) => t.clone(),
            ProgramNode::Operation(o) => o.sig.output.clone(),
            ProgramNode::If => p.args.get(1).unwrap().into(),
        }
    }
}

impl<T: TypeSystemBounds> Display for Program<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.node {
            ProgramNode::Constant(c) => write!(f, "{c}"),
            ProgramNode::Variable(v, _) => write!(f, "{v}"),
            ProgramNode::Operation(o) => write!(
                f,
                "{}({})",
                o,
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

impl<T: TypeSystemBounds> Program<T> {
    pub fn interpret(&self, e: &Environment<T>) -> Result<Constant, InvalidProg> {
        let Program { node, args } = self;
        Ok(match node {
            ProgramNode::Constant(c) => c.clone(),
            ProgramNode::Variable(v, _) => e.get(v).unwrap().clone(),
            ProgramNode::Operation(o) => {
                let args = args.iter().map(|a| a.interpret(e)).try_collect()?;
                o.execute(&args)?
            }
            ProgramNode::If => {
                if args.get(0).unwrap().interpret(e)? == Constant::Bool(true) {
                    args.get(1).unwrap().interpret(e)?
                } else {
                    args.get(2).unwrap().interpret(e)?
                }
            }
        })
    }

    pub fn get_behavior(&self, tests: &Vec<TestCase>) -> Vec<TestCase> {
        tests
            .iter()
            .filter_map(|t| {
                self.interpret(&t.into_env()).ok().map(|output| TestCase {
                    inputs: t.inputs.clone(),
                    output,
                })
            })
            .collect()
    }

    pub fn passes_test_case(&self, t: &TestCase) -> bool {
        self.interpret(&t.into_env())
            .map_or(false, |output| output == t.output)
    }

    pub fn passes_all_test_cases(&self, v: &Vec<TestCase>) -> bool {
        v.iter().all(|t| self.passes_test_case(t))
    }

    pub fn get_type(&self) -> T {
        match &self.node {
            ProgramNode::Constant(c) => c.clone().into(),
            ProgramNode::Variable(_, t) => t.clone(),
            ProgramNode::Operation(o) => o.sig.output.clone(),
            ProgramNode::If => self.args.get(1).unwrap().get_type(),
        }
    }
}
