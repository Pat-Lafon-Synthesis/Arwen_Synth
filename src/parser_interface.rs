use std::ops::{Deref, DerefMut};

use program_synthesis_parser::lang::{
    ActualExp, ActualType, Example, Exp, Problem, SynthProblem, Type,
};

use crate::language::{BaseType, Constant, Signature, TestCase, TypeSystemBounds};

pub fn parse(src: String) -> MySynthProblem<BaseType> {
    let parser = program_synthesis_parser::spec::ProblemParser::new();
    parser.parse(&src).unwrap().into()
}

pub struct Examples {
    pub tests: Vec<TestCase>,
}

impl From<Vec<TestCase>> for Examples {
    fn from(tests: Vec<TestCase>) -> Self {
        Self { tests }
    }
}

impl From<Examples> for Vec<TestCase> {
    fn from(value: Examples) -> Self {
        value.tests
    }
}

impl Deref for Examples {
    type Target = Vec<TestCase>;

    fn deref(&self) -> &Self::Target {
        &self.tests
    }
}

impl DerefMut for Examples {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.tests
    }
}

impl From<&Problem> for Examples {
    fn from(value: &Problem) -> Self {
        match value {
            Problem::UIOEs(x) => Examples {
                tests: x.iter().map(Into::into).collect(),
            },
            Problem::UEquiv(..) | Problem::UPost(_) => unimplemented!(),
        }
    }
}

impl From<&Exp> for Constant {
    fn from(e: &Exp) -> Self {
        match &***e {
            ActualExp::CTor(name, exp) => match (name.as_ref(), &***exp) {
                ("True", ActualExp::Tuple(v)) if v.is_empty() => Constant::Bool(true),
                ("False", ActualExp::Tuple(v)) if v.is_empty() => Constant::Bool(false),
                ("O", ActualExp::Tuple(v)) if v.is_empty() => Constant::Int(0),
                ("S", ActualExp::CTor(..)) => {
                    if let Constant::Int(i) = (exp).into() {
                        Constant::Int(i + 1)
                    } else {
                        panic!()
                    }
                }
                ("Nil", ActualExp::Tuple(v)) if v.is_empty() => Constant::IntList(Vec::new()),
                ("Cons", ActualExp::Tuple(v)) if v.len() == 2 => {
                    if let (Constant::Int(n), Constant::IntList(mut v)) =
                        ((&v[0]).into(), (&v[1]).into())
                    {
                        v.push(n);
                        Constant::IntList(v)
                    } else {
                        panic!()
                    }
                }
                e => {
                    dbg!(&e);
                    unimplemented!()
                }
            },

            ActualExp::Var(_)
            | ActualExp::Wildcard
            | ActualExp::App(..)
            | ActualExp::Func(..)
            | ActualExp::Unctor(..)
            | ActualExp::Eq(..)
            | ActualExp::Match(..)
            | ActualExp::Fix(..)
            | ActualExp::Tuple(_)
            | ActualExp::Proj(..) => unimplemented!(),
        }
    }
}

impl From<&Example> for TestCase {
    fn from(Example { input, output }: &Example) -> Self {
        TestCase {
            inputs: input.iter().map(Into::into).collect(),
            output: output.into(),
        }
    }
}

pub struct MySynthProblem<T: TypeSystemBounds> {
    pub sig: Signature<T>,
    pub tests: Examples,
}

impl From<Type> for BaseType {
    fn from(value: Type) -> Self {
        match &**value {
            ActualType::Named(n) => match n.as_str() {
                "bool" => BaseType::Bool,
                "nat" => BaseType::Int,
                "list" => BaseType::IntList,
                _ => unimplemented!(),
            },
            ActualType::Arrow(..)
            | ActualType::Tuple(_)
            | ActualType::Mu(..)
            | ActualType::Variant(_) => unimplemented!(),
        }
    }
}

fn uncurry_arrow_type(t: Type) -> Vec<BaseType> {
    match &**t {
        ActualType::Arrow(t1, t2) => vec![
            uncurry_arrow_type(t1.clone()),
            uncurry_arrow_type(t2.clone()),
        ]
        .concat(),
        ActualType::Named(_) => vec![t.into()],
        ActualType::Tuple(_) | ActualType::Mu(..) | ActualType::Variant(_) => todo!(),
    }
}

impl From<Type> for Signature<BaseType> {
    fn from(value: Type) -> Self {
        match &**value {
            ActualType::Arrow(..) => {
                let mut typs = uncurry_arrow_type(value);
                let output = typs.pop().unwrap();
                Signature {
                    input: typs,
                    output,
                }
            }
            ActualType::Named(_)
            | ActualType::Tuple(_)
            | ActualType::Mu(..)
            | ActualType::Variant(_) => unimplemented!(),
        }
    }
}

impl From<SynthProblem> for MySynthProblem<BaseType> {
    fn from(
        SynthProblem {
            imports: _,
            decls: _,
            synth_type,
            spec,
        }: SynthProblem,
    ) -> Self {
        MySynthProblem {
            sig: synth_type.into(),
            tests: (&spec).into(),
        }
    }
}
