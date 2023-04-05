use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::rc::Rc;

use itertools::Itertools;

use crate::types::{BaseType, RefinementType, Signature};

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

#[derive(Clone)]
pub struct Operation {
    pub name: String,
    pub sig: Signature<BaseType>,
    pub code: Rc<dyn Fn(&Vec<Constant>) -> Result<Constant, InvalidProg>>,
}

impl Operation {
    pub fn execute(&self, args: &Vec<Constant>) -> Result<Constant, InvalidProg> {
        (self.code)(args)
    }
}

impl Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl std::fmt::Debug for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Operation")
            .field("name", &self.name)
            .field("sig", &self.sig)
            .finish()
    }
}

impl Hash for Operation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl PartialEq for Operation {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Eq for Operation {}

impl PartialOrd for Operation {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.name.partial_cmp(&other.name)
    }
}

impl Ord for Operation {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Variable {
    pub name: String,
    pub ty: RefinementType,
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProgramNode {
    Constant(Constant),
    Variable(Variable, BaseType),
    Operation(Operation),
    If,
}

impl Display for ProgramNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProgramNode::Constant(c) => write!(f, "{c}"),
            ProgramNode::Variable(v, _) => write!(f, "{v}"),
            ProgramNode::Operation(o) => write!(f, "{}", o),
            ProgramNode::If => write!(f, "if"),
        }
    }
}

type Environment = HashMap<Variable, Constant>;

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct TestCase {
    pub inputs: Vec<Constant>,
    pub output: Constant,
}

impl TestCase {
    fn into_env(&self) -> Environment {
        let TestCase { inputs, .. } = self;
        inputs
            .iter()
            .enumerate()
            .map(|(i, c)| {
                (
                    Variable {
                        name: format!("arg{i:?}"),
                        ty: Into::<BaseType>::into(c).into(),
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

pub struct InvalidProg {}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct Program {
    pub node: ProgramNode,
    pub args: Vec<Program>,
}

impl Display for Program {
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

impl Program {
    pub fn interpret(&self, e: &Environment) -> Result<Constant, InvalidProg> {
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
}
