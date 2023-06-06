use arwen_synth::synthesis;

mod libraries;
use arwen_synth::language::Examples;
use arwen_synth::parser_interface::parse;
use libraries::*;
use std::fs::File;
use std::io::Read;

macro_rules! make_test {
    ($test_name:tt, $($libs:tt)*) => {
        #[test_log::test]
        fn $test_name() {
            let mut file =
                File::open(format!("tests/benchmarks/{}.mls", stringify!($test_name))).unwrap();
            let mut buffer = String::new();
            file.read_to_string(&mut buffer).unwrap();
            let synth_problem = parse(buffer);

            let prog = synthesis(
                synth_problem.sig.into(),
                $($libs)*,
                Examples::new(synth_problem.tests.tests, Vec::new()),
                3,
            );
            insta::assert_display_snapshot!(stringify!($test_name), prog.unwrap());
        }
    };
}

make_test!(list_append, &list_library());
make_test!(list_compress, &list_library());
make_test!(list_concat, &list_library());
make_test!(list_drop, &list_library());
make_test!(list_dropeven, &list_library());
make_test!(list_even_parity, &list_library());
make_test!(list_filter, &list_library());
make_test!(list_fold, &list_library());
make_test!(list_hd, &{
    let mut l = list_library();
    l.extend(nat_library());
    l
});
make_test!(list_inc, &list_library());
make_test!(list_last, &list_library());
make_test!(list_last2, &list_library());
make_test!(list_length, &list_library());
make_test!(list_make, &list_library());
make_test!(list_map, &list_library());
make_test!(list_nth, &list_library());
make_test!(list_pairwise, &list_library());
make_test!(list_range, &list_library());
make_test!(list_rev_app, &list_library());
make_test!(list_rev_fold, &list_library());
make_test!(list_rev_snoc, &list_library());
make_test!(list_rev_tailcall, &list_library());
make_test!(list_snoc, &list_library());
make_test!(list_sort_sorted_insert, &list_library());
make_test!(list_sorted_insert, &list_library());
make_test!(list_stutter, &list_library());
make_test!(list_sum, &list_library());
make_test!(list_take, &list_library());
make_test!(list_tl, &list_library());
