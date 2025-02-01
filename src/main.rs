mod lex;
mod parse;

use std::{io::stdout, path::PathBuf, process::exit};

use clap::Parser;
use itertools::Itertools;
use lex::LexImplementation;

#[cfg(test)]
use std::{fs, path::Path};

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Filename
    path: PathBuf,

    #[arg(short)]
    lex: bool,

    #[arg(short)]
    parse: bool,

    #[arg(short)]
    typecheck: bool,
}

fn main() {
    #[allow(unused_mut)]
    let Cli {
        path,
        mut lex,
        mut parse,
        mut typecheck,
    } = Cli::parse();

    #[cfg(feature = "homework")]
    {
        let homework_detect = regex::Regex::new(r"/grader/hw(\d+)/").unwrap();
        if let Some(homework) = homework_detect.captures(&path.display().to_string()) {
            let homework = &homework[1];
            match homework.parse::<u8>() {
                Ok(2) => lex = true,
                Ok(3) => parse = true,
                Ok(4) => parse = true,
                Ok(5) => parse = true,
                Ok(6) => typecheck = true,
                Ok(i) if i > 6 => panic!("Unknown homework {i}"),
                _ => {}
            }
        }
    }

    if typecheck {
        parse = true;
    }

    if parse {
        lex = true;
    }

    let file = match std::fs::read_to_string(&path) {
        Ok(file) => file,
        Err(e) => {
            println!("Compilation failed {e}");
            return;
        }
    };

    if !lex {
        println!("Compilation failed, nothing done");
        return;
    }

    let (tokens, input_by_token) = match lex::LexLinear::lex(&file) {
        Ok(tokens) => tokens,
        #[allow(unused_variables)]
        Err(e) => {
            #[cfg(feature = "homework")]
            println!("Compilation failed");
            #[cfg(not(feature = "homework"))]
            println!("Compilation failed {e}");
            return;
        }
    };

    if !parse {
        let mut output = String::new();
        use std::fmt::Write;

        for token in &tokens {
            writeln!(output, "{}", token).unwrap();
        }
        writeln!(output, "Compilation succeeded").unwrap();

        {
            use std::io::Write;
            stdout().write_all(output.as_bytes()).unwrap();
        }

        exit(0);
    }

    let parsed = match parse::parse(&tokens, &input_by_token, &file, &path) {
        Ok(tokens) => tokens,
        #[allow(unused_variables)]
        Err(e) => {
            #[cfg(feature = "homework")]
            println!("Compilation failed");
            #[cfg(not(feature = "homework"))]
            println!("Compilation failed {e}");
            return;
        }
    };

    if !typecheck {
        let mut output = String::new();
        use std::fmt::Write;

        for parsed in &parsed {
            writeln!(output, "{}", parsed).unwrap();
        }
        writeln!(output, "Compilation succeeded").unwrap();

        {
            use std::io::Write;
            stdout().write_all(output.as_bytes()).unwrap();
        }

        exit(0);
    }

    let _ = parsed;
}

#[derive(Debug, Clone, Copy)]
enum UndoSliceSelection<'a> {
    Boundless,
    Beginning(&'a str),
    End(&'a str),
}

fn undo_slice<'a>(
    original: &'a str,
    a: UndoSliceSelection<'a>,
    b: UndoSliceSelection<'a>,
) -> &'a str {
    fn resolve_idx(
        original: &'_ str,
        undo_selection: UndoSliceSelection<'_>,
        default: usize,
    ) -> usize {
        match undo_selection {
            UndoSliceSelection::Beginning(undo_selection) => {
                undo_selection.as_ptr() as usize - original.as_ptr() as usize
            }
            UndoSliceSelection::End(undo_selection) => {
                undo_selection.as_ptr() as usize + undo_selection.len() - original.as_ptr() as usize
            }
            UndoSliceSelection::Boundless => default,
        }
    }

    let start = resolve_idx(original, a, 0);
    let end = resolve_idx(original, b, original.len());

    assert!(start <= end);

    &original[start..end]
}

#[test]
fn test_undo_slice() {
    let original = "hello world";
    assert_eq!(
        undo_slice(
            original,
            UndoSliceSelection::Boundless,
            UndoSliceSelection::Boundless
        ),
        original
    );

    let slice = &original[1..4];

    assert_eq!(
        undo_slice(
            original,
            UndoSliceSelection::Boundless,
            UndoSliceSelection::End(slice)
        ),
        "hell"
    );

    let slice = &original[1..4];

    assert_eq!(
        undo_slice(
            original,
            UndoSliceSelection::Beginning(slice),
            UndoSliceSelection::End(slice)
        ),
        "ell"
    );

    let slice = &original[1..4];

    assert_eq!(
        undo_slice(
            original,
            UndoSliceSelection::Boundless,
            UndoSliceSelection::Beginning(slice),
        ),
        "h"
    );
}

fn undo_slice_by_cuts<'a, const N: usize, const M: usize>(
    original: &'a str,
    cuts: [UndoSliceSelection<'a>; N],
) -> [&'a str; M] {
    const {
        assert!(N - 1 == M);
    }

    cuts.iter()
        .tuple_windows()
        .map(|(a, b)| undo_slice(original, *a, *b))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

#[cfg(test)]
fn test_correct(directory: &str, mut tester: impl FnMut(&str, &str)) {
    use std::{fs, path::Path};
    let folder = Path::new(directory);
    if !folder.exists() {
        panic!("Could not find {}", folder.display());
    }

    let mut all_test_paths = vec![];
    let mut all_solution_paths = vec![];

    let test_paths = fs::read_dir(folder).unwrap();

    let test_paths = test_paths
        .flatten()
        .filter(|f| f.file_type().unwrap().is_file())
        .filter(|f| f.path().extension().unwrap() == "jpl");
    for test_path in test_paths {
        let test_path = test_path.path();
        let mut solution_path = test_path.clone();
        // add .expected to the end of the path
        solution_path.set_extension("jpl.expected");

        all_test_paths.push(test_path);
        all_solution_paths.push(solution_path);
    }

    for (test_path, solution_path) in all_test_paths.iter().zip(all_solution_paths.iter()) {
        println!("{}", test_path.display());
        println!("{}", solution_path.display());
        let file = fs::read_to_string(test_path).unwrap();
        let solution_file = fs::read_to_string(solution_path).unwrap();

        println!("{}", file);

        tester(&file, &solution_file);
    }
}

#[cfg(test)]
fn test_solos(directory: &str, mut tester: impl FnMut(&str, &Path)) {
    let folder = Path::new(directory);
    if !folder.exists() {
        panic!("Could not find {}", folder.display());
    }

    let test_paths = fs::read_dir(folder)
        .unwrap()
        .flatten()
        .filter(|f| f.file_type().unwrap().is_file())
        .filter(|f| f.path().extension().unwrap() == "jpl");

    for test_path in test_paths {
        let test_path = test_path.path();
        println!("{}", test_path.display());
        if let Ok(file) = fs::read_to_string(&test_path) {
            tester(&file, &test_path);
        }
    }
}
