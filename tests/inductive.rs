use arwen_synth::{
    language::{BaseType, Constant, Examples, Signature, TestCase},
    libraries::*,
    synthesis,
};

#[test]
fn inductive_synthesis_negation() {
    let sig = Signature {
        input: vec![BaseType::Bool],
        output: BaseType::Bool,
    };

    let positive_examples = vec![TestCase {
        inputs: vec![Constant::Bool(true)],
        output: Constant::Bool(false),
    }];

    let negative_examples = vec![TestCase {
        inputs: vec![Constant::Bool(false)],
        output: Constant::Bool(false),
    }];

    let prog = synthesis(
        sig,
        &bool_library(),
        Examples::new(positive_examples, negative_examples),
        3,
    );
    insta::assert_display_snapshot!("inductive_synthesis_negation", prog.unwrap());
}
