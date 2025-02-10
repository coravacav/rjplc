use super::typecheck;
use crate::{measure::print_timings, parse::parse, test_correct, test_solos, CustomDisplay};
use std::path::Path;

#[test]
fn test_parse_correct() {
    use regex::Regex;
    let regex = Regex::new(r"\n\s+").unwrap();

    let tester = |file: &str, solution_file: &str| {
        let (tokens, string_map) = crate::lex::lex(file).expect("Lexing should work");

        let mut cmds = match parse(&tokens, &string_map, file, Path::new("")) {
            Ok(cmds) => cmds,
            Err(e) => {
                panic!("Compilation failed {e}");
            }
        };

        if let Err(e) = typecheck(&mut cmds, &string_map) {
            panic!("Typechecking failed {e}");
        }

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

    test_correct("grader/hw6/ok", tester);
    test_correct("grader/hw6/ok-fuzzer", tester);
    print_timings();
}

#[test]
fn test_parse_fails() {
    let tester = |file: &str, file_path: &Path| {
        let Ok((tokens, string_map)) = crate::lex::lex(file) else {
            return;
        };

        let Ok(mut cmds) = parse(&tokens, &string_map, file, file_path) else {
            return;
        };

        match typecheck(&mut cmds, &string_map) {
            Ok(()) => {
                panic!("expected parse to fail");
            }
            Err(e) => {
                #[cfg(not(feature = "measure"))]
                println!("Compilation failed {e:?}");
            }
        }
    };

    test_solos("grader/hw6/fail-fuzzer1", tester);
    test_solos("grader/hw6/fail-fuzzer2", tester);
    test_solos("grader/hw6/fail-fuzzer3", tester);
    print_timings();
}
