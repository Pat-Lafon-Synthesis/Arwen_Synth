use arwen_synth::{language::*, synthesis};

mod libraries;
use libraries::*;

#[test]
fn list_append() {
    let sig = Signature {
        input: vec![BaseType::IntList, BaseType::IntList],
        output: BaseType::IntList,
    };

    let tests = vec![
        TestCase {
            inputs: vec![Constant::IntList(Vec::new()), Constant::IntList(Vec::new())],
            output: Constant::IntList(Vec::new()),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0, 1]), Constant::IntList(Vec::new())],
            output: Constant::IntList(vec![0, 1]),
        },
        TestCase {
            inputs: vec![Constant::IntList(Vec::new()), Constant::IntList(vec![0, 1])],
            output: Constant::IntList(vec![0, 1]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0]), Constant::IntList(vec![0, 1])],
            output: Constant::IntList(vec![0, 0, 1]),
        },
    ];

    let mut library = bool_library();
    library.append(&mut list_library());

    let prog = synthesis(sig.into(), &library, tests, 1);
    assert!(prog.is_some());
    println!("{}", prog.unwrap())
}

#[test]
fn list_compress() {
    let sig = Signature {
        input: vec![BaseType::IntList],
        output: BaseType::IntList,
    };

    let tests = vec![
        TestCase {
            inputs: vec![Constant::IntList(Vec::new())],
            output: Constant::IntList(Vec::new()),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![1])],
            output: Constant::IntList(vec![1]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0])],
            output: Constant::IntList(vec![0]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0, 0])],
            output: Constant::IntList(vec![0, 0]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![1, 1])],
            output: Constant::IntList(vec![1, 1]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0, 2])],
            output: Constant::IntList(vec![0, 2]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0, 0, 1])],
            output: Constant::IntList(vec![0, 1]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![1, 1, 0])],
            output: Constant::IntList(vec![1, 0]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0, 0, 1, 2])],
            output: Constant::IntList(vec![0, 1, 2]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0, 0, 1, 2, 2])],
            output: Constant::IntList(vec![0, 1, 2]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0, 2, 2])],
            output: Constant::IntList(vec![0, 2]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0, 2, 2, 2])],
            output: Constant::IntList(vec![0, 2]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0, 2, 2, 2, 1])],
            output: Constant::IntList(vec![0, 2, 1]),
        },
    ];

    let mut library = bool_library();
    library.append(&mut list_library());
    library.append(&mut int_library());

    let prog = synthesis(sig.into(), &library, tests, 1);
    assert!(prog.is_some());
    println!("{}", prog.unwrap())
}

fn list_concat() {
    // List of lists
    todo!()
}

#[test]
fn list_drop() {
    let sig = Signature {
        input: vec![BaseType::IntList, BaseType::Int],
        output: BaseType::IntList,
    };

    let tests = vec![
        TestCase {
            inputs: vec![Constant::IntList(vec![]), Constant::Int(0)],
            output: Constant::IntList(vec![]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![1]), Constant::Int(0)],
            output: Constant::IntList(vec![1]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![1]), Constant::Int(1)],
            output: Constant::IntList(vec![]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0, 1]), Constant::Int(1)],
            output: Constant::IntList(vec![0]),
        },
        TestCase {
            inputs: vec![Constant::IntList(vec![0, 1]), Constant::Int(2)],
            output: Constant::IntList(vec![]),
        },
    ];

    let mut library = int_library();
    library.append(&mut list_library());


    let prog = synthesis(sig.into(), &library, tests, 1);
    assert!(prog.is_some());
    println!("{}", prog.unwrap())
}
