use arwen_synth::{
    data_structures::create_ecta_from_traces,
    language::{LinearProgram, LinearProgramNode, Variable},
    types::BaseType,
};
use ecta_rs::ECTA;
mod libraries;
use libraries::*;
use log::info;

#[test_log::test]
fn test_ecta_conversion() {
    let nat = nat_library();
    let lib = list_library();

    #[allow(non_snake_case)]
    let O = nat.iter().find(|o| o.name == "O").unwrap();
    let inc = nat.iter().find(|o| o.name == "inc").unwrap();
    let hd = lib.iter().find(|o| o.name == "hd").unwrap();
    let tail = lib.iter().find(|o| o.name == "tail").unwrap();
    let cons = lib.iter().find(|o| o.name == "cons").unwrap();
    let nil = lib.iter().find(|o| o.name == "nil").unwrap();
    let arg0 = LinearProgram {
        node: LinearProgramNode::Variable(Variable {
            name: "arg0".to_string(),
            ty: BaseType::IntList,
        }),
        args: vec![],
    };

    let mut ecta = ECTA::new();

    // O()
    let p1 = LinearProgram::<BaseType>::new(LinearProgramNode::Operation(O.clone()), vec![]);
    // inc(O())
    let p2 =
        LinearProgram::<BaseType>::new(LinearProgramNode::Operation(inc.clone()), vec![p1.clone()]);
    // hd(arg0)
    let p3 = LinearProgram::<BaseType>::new(
        LinearProgramNode::Operation(hd.clone()),
        vec![arg0.clone()],
    );
    // inc(inc(O()))
    let p4 =
        LinearProgram::<BaseType>::new(LinearProgramNode::Operation(inc.clone()), vec![p2.clone()]);

    let tail_a0 = LinearProgram::new(
        LinearProgramNode::Operation(tail.clone()),
        vec![arg0.clone()],
    );
    let cons_1_tail_a0 = LinearProgram::new(
        LinearProgramNode::Operation(cons.clone()),
        vec![p2.clone(), tail_a0.clone()],
    );

    // hd(cons(inc(O()),tail(arg0)))
    let p5 = LinearProgram::<BaseType>::new(
        LinearProgramNode::Operation(hd.clone()),
        vec![cons_1_tail_a0],
    );

    //inc(hd(tail(arg0)))
    let hd_tail_a0 = LinearProgram::new(LinearProgramNode::Operation(hd.clone()), vec![tail_a0]);
    let p6 =
        LinearProgram::<BaseType>::new(LinearProgramNode::Operation(inc.clone()), vec![hd_tail_a0]);

    let cons_0_nil = LinearProgram::new(
        LinearProgramNode::Operation(cons.clone()),
        vec![
            p1.clone(),
            LinearProgram::new(LinearProgramNode::Operation(nil.clone()), vec![]),
        ],
    );
    let hd_a0 = LinearProgram::new(LinearProgramNode::Operation(hd.clone()), vec![arg0]);

    // hd(cons(inc(inc(O())),cons(hd(arg0),cons(O(),nil()))))
    let p7 = LinearProgram::<BaseType>::new(
        LinearProgramNode::Operation(hd.clone()),
        vec![LinearProgram::new(
            LinearProgramNode::Operation(cons.clone()),
            vec![
                p4.clone(),
                LinearProgram::new(
                    LinearProgramNode::Operation(cons.clone()),
                    vec![hd_a0, cons_0_nil],
                ),
            ],
        )],
    );

    let mut frags = vec![&p1, &p2, &p3, &p4, &p5, &p6, &p7];

    create_ecta_from_traces(&mut ecta, &mut frags);

    info!("Ecta = {}", ecta.get_dot(&[]));

    insta::assert_display_snapshot!("conversion_1", ecta.get_dot(&[]).to_string());
}

#[test_log::test]
fn test_ecta_conversion_2() {
    let bool = bool_library();

    let b_true = bool.iter().find(|o| o.name == "true").unwrap();
    let b_false = bool.iter().find(|o| o.name == "false").unwrap();
    let b_and = bool.iter().find(|o| o.name == "and").unwrap();
    let b_or = bool.iter().find(|o| o.name == "or").unwrap();
    let b_not = bool.iter().find(|o| o.name == "not").unwrap();

    let mut ecta = ECTA::new();

    let arg0 = LinearProgram::new(
        LinearProgramNode::Variable(Variable {
            name: "arg0".to_string(),
            ty: BaseType::Bool,
        }),
        Vec::new(),
    );

    let arg1 = LinearProgram::new(
        LinearProgramNode::Variable(Variable {
            name: "arg1".to_string(),
            ty: BaseType::Bool,
        }),
        Vec::new(),
    );

    let p_true = LinearProgram::new(LinearProgramNode::Operation(b_true.clone()), Vec::new());

    let p_false = LinearProgram::new(LinearProgramNode::Operation(b_false.clone()), Vec::new());

    let not_arg0 = LinearProgram::new(
        LinearProgramNode::Operation(b_not.clone()),
        vec![arg0.clone()],
    );

    let not_arg1 = LinearProgram::new(
        LinearProgramNode::Operation(b_not.clone()),
        vec![arg1.clone()],
    );

    let and_arg0_arg1 = LinearProgram::new(
        LinearProgramNode::Operation(b_and.clone()),
        vec![arg0.clone(), arg1.clone()],
    );

    let or_arg0_arg1 = LinearProgram::new(
        LinearProgramNode::Operation(b_or.clone()),
        vec![arg0.clone(), arg1.clone()],
    );

    let and_not_arg0_not_arg1 = LinearProgram::new(
        LinearProgramNode::Operation(b_and.clone()),
        vec![not_arg0.clone(), not_arg1.clone()],
    );

    let and_not_arg0_arg1 = LinearProgram::new(
        LinearProgramNode::Operation(b_and.clone()),
        vec![not_arg0.clone(), arg1.clone()],
    );

    let and_not_arg1_arg0 = LinearProgram::new(
        LinearProgramNode::Operation(b_and.clone()),
        vec![not_arg1.clone(), arg0.clone()],
    );

    let mut frags = vec![
        &arg0,
        &arg1,
        &p_true,
        &p_false,
        &not_arg0,
        &not_arg1,
        &and_arg0_arg1,
        &or_arg0_arg1,
        &and_not_arg0_not_arg1,
        &and_not_arg0_arg1,
        &and_not_arg1_arg0,
    ];

    create_ecta_from_traces(&mut ecta, &mut frags);

    info!("Ecta = {}", ecta.get_dot(&[]));

    insta::assert_display_snapshot!("conversion_2", ecta.get_dot(&[]).to_string());
}
