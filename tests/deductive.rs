use std::rc::Rc;

use arwen_synth::{
    language::{Constant, Examples, Operation},
    synthesis,
    types::{BaseType, Predicate, PredicateExpression, RefinementType, Signature},
};

#[test]
fn deductive_synthesis_zero() {
    let sig = Signature {
        input: vec![],
        output: RefinementType {
            ty: BaseType::Int,
            p: Predicate::Equal(
                PredicateExpression::Const(0.into()).into(),
                PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
            ),
        },
    };
    let tests = Examples::new(Vec::new());

    let l = vec![Operation {
        name: "zero".to_string(),
        sig: Signature {
            input: vec![],
            output: RefinementType {
                ty: BaseType::Int,
                p: Predicate::Equal(
                    PredicateExpression::Const(0.into()).into(),
                    PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                ),
            },
        },
        code: Rc::new(|args: &Vec<_>| Ok(Constant::Int(0))),
    }];

    let prog = synthesis(sig, &l, tests, 3);

    insta::assert_display_snapshot!("easy_deductive_synth", prog.unwrap());
}

#[test]
fn deductive_synthesis_one() {
    let sig = Signature {
        input: vec![],
        output: RefinementType {
            ty: BaseType::Int,
            p: Predicate::Equal(
                PredicateExpression::Const(1.into()).into(),
                PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
            ),
        },
    };
    let tests = Examples::new(Vec::new());

    let l = vec![
        Operation {
            name: "inc".to_string(),
            sig: Signature {
                input: vec![RefinementType {
                    ty: BaseType::Int,
                    p: Predicate::True,
                }],
                output: RefinementType {
                    ty: BaseType::Int,
                    p: Predicate::Equal(
                        PredicateExpression::Plus(
                            PredicateExpression::Var("a".to_string(), BaseType::Int.into()).into(),
                            PredicateExpression::Const(1.into()).into(),
                        )
                        .into(),
                        PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                    ),
                },
            },
            code: Rc::new(|args: &Vec<_>| (&args[0]).try_into().map(|i: i64| (i + 1).into())),
        },
        Operation {
            name: "zero".to_string(),
            sig: Signature {
                input: vec![],
                output: RefinementType {
                    ty: BaseType::Int,
                    p: Predicate::Equal(
                        PredicateExpression::Const(0.into()).into(),
                        PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                    ),
                },
            },
            code: Rc::new(|args: &Vec<_>| Ok(Constant::Int(0))),
        },
    ];

    let prog = synthesis(sig, &l, tests, 3);

    insta::assert_display_snapshot!("easy_deductive_synth", prog.unwrap());
}
