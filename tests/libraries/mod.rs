use std::rc::Rc;

use arwen_synth::{
    language::*,
    types::{BaseType, Signature},
};

#[allow(dead_code)]
pub fn bool_library() -> Vec<Operation<BaseType>> {
    vec![
        Operation {
            name: "true".to_string(),
            sig: Signature {
                input: vec![],
                output: BaseType::Bool,
            },
            code: Rc::new(|_: &Vec<_>| Ok(Constant::Bool(true))),
        },
        Operation {
            name: "false".to_string(),
            sig: Signature {
                input: vec![],
                output: BaseType::Bool,
            },
            code: Rc::new(|_| Ok(Constant::Bool(false))),
        },
        Operation {
            name: "and".to_string(),
            sig: Signature {
                input: vec![BaseType::Bool, BaseType::Bool],
                output: BaseType::Bool,
            },
            code: Rc::new(|args| match (args.get(0).unwrap(), args.get(1).unwrap()) {
                (Constant::Bool(b1), Constant::Bool(b2)) => Ok(Constant::Bool(*b1 && *b2)),
                _ => panic!(),
            }),
        },
        Operation {
            name: "or".to_string(),
            sig: Signature {
                input: vec![BaseType::Bool, BaseType::Bool],
                output: BaseType::Bool,
            },
            code: Rc::new(|args| match (args.get(0).unwrap(), args.get(1).unwrap()) {
                (Constant::Bool(b1), Constant::Bool(b2)) => Ok(Constant::Bool(*b1 || *b2)),
                _ => panic!(),
            }),
        },
        Operation {
            name: "not".to_string(),
            sig: Signature {
                input: vec![BaseType::Bool],
                output: BaseType::Bool,
            },
            code: Rc::new(|args| match args.get(0).unwrap() {
                Constant::Bool(b1) => Ok(Constant::Bool(!*b1)),
                _ => panic!(),
            }),
        },
    ]
}

#[allow(dead_code)]
pub fn nat_library() -> Vec<Operation<BaseType>> {
    vec![
        Operation {
            name: "O".to_string(),
            sig: Signature {
                input: vec![],
                output: BaseType::Int,
            },
            code: Rc::new(|_: &Vec<_>| Ok(Constant::Int(0))),
        },
        Operation {
            name: "is_zero".to_string(),
            sig: Signature {
                input: vec![BaseType::Int],
                output: BaseType::Bool,
            },
            code: Rc::new(|args| match args.get(0).unwrap() {
                Constant::Int(x) => Ok(Constant::Bool(x == &0)),
                _ => panic!(),
            }),
        },
        Operation {
            name: "inc".to_string(),
            sig: Signature {
                input: vec![BaseType::Int],
                output: BaseType::Int,
            },
            code: Rc::new(|args| match args.get(0).unwrap() {
                Constant::Int(x) => Ok(Constant::Int(x + 1)),
                _ => panic!(),
            }),
        },
        Operation {
            name: "dec".to_string(),
            sig: Signature {
                input: vec![BaseType::Int],
                output: BaseType::Int,
            },
            code: Rc::new(|args| match args.get(0).unwrap() {
                Constant::Int(x) if *x == 0 => Err(InvalidProg {}),
                Constant::Int(x) => Ok(Constant::Int(x - 1)),
                _ => panic!(),
            }),
        },
        Operation {
            name: "lt".to_string(),
            sig: Signature {
                input: vec![BaseType::Int, BaseType::Int],
                output: BaseType::Bool,
            },
            code: Rc::new(|args| match (args.get(0).unwrap(), args.get(1).unwrap()) {
                (Constant::Int(x), Constant::Int(y)) => Ok(Constant::Bool(x < y)),
                (..) => panic!(),
            }),
        },
        Operation {
            name: "gt".to_string(),
            sig: Signature {
                input: vec![BaseType::Int, BaseType::Int],
                output: BaseType::Bool,
            },
            code: Rc::new(|args| match (args.get(0).unwrap(), args.get(1).unwrap()) {
                (Constant::Int(x), Constant::Int(y)) => Ok(Constant::Bool(x > y)),
                (..) => panic!(),
            }),
        },
        Operation {
            name: "eq".to_string(),
            sig: Signature {
                input: vec![BaseType::Int, BaseType::Int],
                output: BaseType::Bool,
            },
            code: Rc::new(|args| match (args.get(0).unwrap(), args.get(1).unwrap()) {
                (Constant::Int(x), Constant::Int(y)) => Ok(Constant::Bool(x == y)),
                (..) => panic!(),
            }),
        },
    ]
}

#[allow(dead_code)]
pub fn list_library() -> Vec<Operation<BaseType>> {
    vec![
        Operation {
            name: "nil".to_string(),
            sig: Signature {
                input: vec![],
                output: BaseType::IntList,
            },
            code: Rc::new(|_| Ok(Constant::IntList(Vec::new()))),
        },
        Operation {
            name: "cons".to_string(),
            sig: Signature {
                input: vec![BaseType::Int, BaseType::IntList],
                output: BaseType::IntList,
            },
            code: Rc::new(|args| match (args.get(0).unwrap(), args.get(1).unwrap()) {
                (Constant::Int(i), Constant::IntList(l)) => {
                    let mut l2 = l.clone();
                    l2.push(*i);
                    Ok(Constant::IntList(l2))
                }
                _ => panic!(),
            }),
        },
        Operation {
            name: "is_nil".to_string(),
            sig: Signature {
                input: vec![BaseType::IntList],
                output: BaseType::Bool,
            },
            code: Rc::new(|args| match args.get(0).unwrap() {
                Constant::IntList(l) => Ok(Constant::Bool(l.is_empty())),
                _ => panic!(),
            }),
        },
        Operation {
            name: "is_cons".to_string(),
            sig: Signature {
                input: vec![BaseType::IntList],
                output: BaseType::Bool,
            },
            code: Rc::new(|args| match args.get(0).unwrap() {
                Constant::IntList(l) => Ok(Constant::Bool(!l.is_empty())),
                _ => panic!(),
            }),
        },
        Operation {
            name: "hd".to_string(),
            sig: Signature {
                input: vec![BaseType::IntList],
                output: BaseType::Int,
            },
            code: Rc::new(|args| match args.get(0).unwrap() {
                Constant::IntList(l) if l.is_empty() => Err(InvalidProg {}),
                Constant::IntList(l) => Ok(Constant::Int(*l.last().unwrap())),
                _ => panic!(),
            }),
        },
        Operation {
            name: "tail".to_string(),
            sig: Signature {
                input: vec![BaseType::IntList],
                output: BaseType::IntList,
            },
            code: Rc::new(|args| match args.get(0).unwrap() {
                Constant::IntList(l) if l.is_empty() => Err(InvalidProg {}),
                Constant::IntList(l) => {
                    let mut x = l.clone();
                    x.pop();
                    Ok(Constant::IntList(x))
                }
                _ => panic!(),
            }),
        },
    ]
}
