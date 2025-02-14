use super::parse;
use crate::{measure::print_timings, test_correct, test_solos, CustomDisplay};
use std::path::Path;

#[test]
fn test_parse_correct() {
    use regex::Regex;
    let regex = Regex::new(r"\n\s+").unwrap();

    let tester = |file: &str, solution_file: &str| {
        let (tokens, string_map) = crate::lex::lex(file).expect("Lexing should work");

        let (cmds, _) = parse(&tokens, &string_map, file, Path::new("")).unwrap();

        let mut output = String::new();

        for cmd in cmds {
            cmd.fmt(&mut output, &string_map).unwrap();
            output.push('\n');
        }

        if output == solution_file {
            pretty_assertions::assert_eq!(output, solution_file);
        } else {
            let output = regex.replace_all(&output, " ");
            let solution_file = regex.replace_all(solution_file, " ");
            pretty_assertions::assert_eq!(output, solution_file);
        }
    };

    test_correct("grader/hw3/ok", tester);
    test_correct("grader/hw3/ok-fuzzer", tester);
    test_correct("grader/hw4/ok", tester);
    test_correct("grader/hw4/ok-fuzzer", tester);
    test_correct("grader/hw5/ok", tester);
    test_correct("grader/hw5/ok-fuzzer", tester);
    print_timings();
}

#[test]
fn test_parse_fails() {
    let tester = |file: &str, file_path: &Path| {
        let Ok((tokens, string_map)) = crate::lex::lex(file) else {
            return;
        };

        match parse(&tokens, &string_map, file, file_path) {
            Ok(parsed) => {
                println!("{parsed:?}");
                panic!("expected parse to fail");
            }
            Err(e) => {
                #[cfg(not(feature = "measure"))]
                println!("Compilation failed {e:?}");
            }
        }
    };

    test_solos("grader/hw3/fail-fuzzer1", tester);
    test_solos("grader/hw3/fail-fuzzer2", tester);
    test_solos("grader/hw3/fail-fuzzer3", tester);
    test_solos("grader/hw4/fail-fuzzer1", tester);
    test_solos("grader/hw4/fail-fuzzer2", tester);
    test_solos("grader/hw4/fail-fuzzer3", tester);
    test_solos("grader/hw5/fail-fuzzer1", tester);
    test_solos("grader/hw5/fail-fuzzer2", tester);
    test_solos("grader/hw5/fail-fuzzer3", tester);
    print_timings();
}
