use std::vec;

use arwen_synth::{
    data_structures::MinHeap,
    language::{Program, ProgramNode, Sketch, Variable},
    types::BaseType,
};
use log::info;

mod libraries;
use libraries::*;

#[test_log::test]
fn sketch_order() {
    let mut heap = MinHeap::new();

    let nat = nat_library();
    let list = list_library();

    let o = nat.iter().find(|o| o.name == "O").unwrap().clone();

    let is_cons = list.iter().find(|o| o.name == "is_cons").unwrap().clone();

    let is_nil = list.iter().find(|o| o.name == "is_nil").unwrap().clone();

    let is_zero = nat.iter().find(|o| o.name == "is_zero").unwrap().clone();

    let hd = list.iter().find(|o| o.name == "hd").unwrap().clone();

    let tail = list.iter().find(|o| o.name == "tail").unwrap().clone();

    let nil = list.iter().find(|o| o.name == "nil").unwrap().clone();

    let arg0 = Program {
        node: ProgramNode::Variable(Variable {
            name: "arg0".to_string(),
            ty: BaseType::IntList,
        }),
        args: Vec::new(),
    };

    let c1 = Program {
        node: ProgramNode::Operation(is_cons.clone()),
        args: vec![Program {
            node: ProgramNode::Operation(nil),
            args: Vec::new(),
        }],
    };

    let c2 = Program {
        node: ProgramNode::Operation(is_nil),
        args: vec![arg0.clone()],
    };

    let c3 = Program {
        node: ProgramNode::Operation(is_zero),
        args: vec![Program {
            node: ProgramNode::Operation(hd),
            args: vec![arg0.clone()],
        }],
    };

    // is_cons(tail(tail(arg0)))
    let c4 = Program {
        node: ProgramNode::Operation(is_cons),
        args: vec![Program {
            node: ProgramNode::Operation(tail.clone()),
            args: vec![Program {
                node: ProgramNode::Operation(tail),
                args: vec![arg0.clone()],
            }],
        }],
    };

    heap.push(Sketch::If(
        Box::new(c1),
        Box::new(Sketch::Operation(o.clone(), Vec::new())),
        Box::new(Sketch::Hole(BaseType::Int)),
    ));
    heap.push(Sketch::If(
        Box::new(c2),
        Box::new(Sketch::Operation(o.clone(), Vec::new())),
        Box::new(Sketch::Hole(BaseType::Int)),
    ));
    heap.push(Sketch::If(
        Box::new(c3),
        Box::new(Sketch::Operation(o.clone(), Vec::new())),
        Box::new(Sketch::Hole(BaseType::Int)),
    ));
    heap.push(Sketch::If(
        Box::new(c4),
        Box::new(Sketch::Operation(o, Vec::new())),
        Box::new(Sketch::Hole(BaseType::Int)),
    ));

    info!("Heap = {heap}");

    insta::assert_display_snapshot!("sketch_order", heap.to_string());
}
