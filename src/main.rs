mod lex;
mod parse;

use std::path::PathBuf;

use clap::Parser;

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
    let Cli {
        path,
        mut lex,
        mut parse,
        typecheck,
    } = Cli::parse();

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

    let mut tokens = vec![];
    let mut parsed = vec![];

    if lex {
        tokens = match lex::lex(&file) {
            Ok(tokens) => tokens,
            Err(e) => {
                println!("Compilation failed {e}");
                return;
            }
        };

        if !parse {
            for token in &tokens {
                println!("{}", token);
            }
        }
    }

    if parse {
        parsed = match parse::parse(&tokens) {
            Ok(tokens) => tokens,
            Err(e) => {
                println!("Compilation failed {e}");
                return;
            }
        };

        if !typecheck {
            for parsed in &parsed {
                println!("{}", parsed);
            }
        }
    }

    let _ = parsed;

    println!("Compilation succeeded")
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
fn test_solos(directory: &str, mut tester: impl FnMut(Option<&str>)) {
    use std::{fs, path::Path};
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
        if let Ok(file) = fs::read_to_string(test_path) {
            tester(Some(&file));
        } else {
            tester(None);
        }
    }
}
