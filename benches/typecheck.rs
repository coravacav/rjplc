use std::{fs, path::Path};

use divan::Bencher;
use itertools::Itertools;
use rjplc::{get_test_paths, lex::lex, parse::parse, typecheck::typecheck as compiler_typecheck};

fn main() {
    // Run registered benchmarks.
    divan::main();
}

// Register a `fibonacci` function and benchmark it over multiple cases.
#[divan::bench]
fn typecheck(bencher: Bencher) {
    let all_test_paths = [
        get_test_paths("grader/hw6/ok"),
        get_test_paths("grader/hw6/ok-fuzzer"),
        get_test_paths("grader/hw7/ok"),
        get_test_paths("grader/hw7/ok-fuzzer"),
    ]
    .iter()
    .flatten()
    .map(|test_path| fs::read_to_string(test_path).unwrap())
    .collect_vec();

    bencher.bench_local(move || {
        for file in &all_test_paths {
            let (tokens, string_map) = lex(std::hint::black_box(file)).expect("Lexing should work");

            let (mut cmds, tokens_consumed) =
                parse(&tokens, &string_map, file, Path::new("")).unwrap();

            if let Err(e) = compiler_typecheck(&mut cmds, &string_map, &tokens_consumed) {
                panic!("Typechecking failed {e}");
            }
        }
    });
}
