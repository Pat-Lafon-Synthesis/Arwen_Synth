use std::rc::Rc;

use arwen_synth::{
    language::{
        BaseType, Constant, Examples, InnerPredicate, Operation, Predicate, PredicateExpression,
        RefinementType, Signature,
    },
    synthesis,
};

#[test]
fn deductive_synthesis_zero() {
    let sig = Signature {
        input: vec![],
        output: RefinementType {
            ty: BaseType::Int,
            p: InnerPredicate::Equal(
                PredicateExpression::Const(0.into()).into(),
                PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
            )
            .into(),
        },
    };
    let tests = Examples::new(Vec::new(), Vec::new());

    let l = vec![Operation {
        name: "zero".to_string(),
        sig: Signature {
            input: vec![],
            output: RefinementType {
                ty: BaseType::Int,
                p: InnerPredicate::Equal(
                    PredicateExpression::Const(0.into()).into(),
                    PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                )
                .into(),
            },
        },
        code: Rc::new(|_args: &Vec<_>| Ok(Constant::Int(0))),
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
            p: InnerPredicate::Equal(
                PredicateExpression::Const(1.into()).into(),
                PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
            )
            .into(),
        },
    };
    let tests = Examples::new(Vec::new(), Vec::new());

    let l = vec![
        Operation {
            name: "inc".to_string(),
            sig: Signature {
                input: vec![RefinementType {
                    ty: BaseType::Int,
                    p: InnerPredicate::Bool(true).into(),
                }],
                output: RefinementType {
                    ty: BaseType::Int,
                    p: InnerPredicate::Equal(
                        PredicateExpression::Plus(
                            PredicateExpression::Var("a".to_string(), BaseType::Int.into()).into(),
                            PredicateExpression::Const(1.into()).into(),
                        )
                        .into(),
                        PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                    )
                    .into(),
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
                    p: InnerPredicate::Equal(
                        PredicateExpression::Const(0.into()).into(),
                        PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                    )
                    .into(),
                },
            },
            code: Rc::new(|_args: &Vec<_>| Ok(Constant::Int(0))),
        },
    ];

    let prog = synthesis(sig, &l, tests, 3);

    insta::assert_display_snapshot!("easy_deductive_synth", prog.unwrap());
}
