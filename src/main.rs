use std::rc::Rc;

use arwen_synth::{
    language::{Constant, InvalidProg, Operation, TestCase},
    synthesis,
    types::{BaseType, Signature},
};

pub fn main() {
    let s = Signature {
        input: vec![BaseType::Int, BaseType::Int],
        output: BaseType::Int,
    };
    let l = vec![
        Operation {
            name: "inc".to_string(),
            sig: Signature {
                input: vec![BaseType::Int],
                output: BaseType::Int,
            },
            code: Rc::new(|args: &Vec<_>| match args.get(0).unwrap() {
                Constant::Int(i) => Ok(Constant::Int(i + 1)),
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
                Constant::Int(0) => Err(InvalidProg {}),
                Constant::Int(i) => Ok(Constant::Int(i - 1)),
                _ => panic!(),
            }),
        },
        Operation {
            name: "is_zero".to_string(),
            sig: Signature {
                input: vec![BaseType::Int],
                output: BaseType::Bool,
            },
            code: Rc::new(|args| match args.get(0).unwrap() {
                Constant::Int(i) => Ok(Constant::Bool(*i == 0)),
                _ => panic!(),
            }),
        },
    ];
    let tc = vec![
        TestCase {
            inputs: vec![Constant::Int(1), Constant::Int(1)],
            output: Constant::Int(2),
        },
        TestCase {
            inputs: vec![Constant::Int(0), Constant::Int(0)],
            output: Constant::Int(0),
        },
        TestCase {
            inputs: vec![Constant::Int(1), Constant::Int(2)],
            output: Constant::Int(3),
        },
        TestCase {
            inputs: vec![Constant::Int(1), Constant::Int(0)],
            output: Constant::Int(1),
        },
    ];

    let prog = synthesis(s.into(), &l, &tc, 4);
    println!("{prog:?}")
}
