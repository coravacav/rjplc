#![deny(clippy::pedantic)]

use std::{io::stdout, path::PathBuf, process::exit};

use clap::Parser;
use measure::print_timings;
use rjplc::{lex, measure, parse, CustomDisplay};

#[derive(Parser)]
#[command(version, about, long_about = None)]
#[allow(clippy::struct_excessive_bools)]
struct Cli {
    /// Filename
    path: PathBuf,

    #[arg(short)]
    lex: bool,

    #[arg(short)]
    parse: bool,

    #[arg(short)]
    typecheck: bool,

    #[arg(short)]
    quiet: bool,

    /// A flag to repeat each operation 100 times to help for accurate measurements
    #[cfg(feature = "measure")]
    #[arg(short, long, action = clap::ArgAction::Count)]
    measure_repeat: u8,
}

#[allow(clippy::too_many_lines)]
fn main() {
    #[allow(unused_mut)]
    let Cli {
        path,
        mut lex,
        mut parse,
        mut typecheck,
        quiet,
        #[cfg(feature = "measure")]
        measure_repeat,
    } = Cli::parse();

    #[cfg(feature = "measure")]
    let reps = if measure_repeat > 0 {
        let reps = 10u128.pow(measure_repeat as u32);
        measure::set_measure_iterations(reps);
        reps - 1 // To make the division accurate.
    } else {
        0
    };

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

    let (tokens, input_by_token, string_map) = match lex::lex(&file) {
        Ok(tokens) => tokens,
        #[allow(unused_variables)]
        Err(e) => {
            #[cfg(feature = "homework")]
            println!("Compilation failed");
            #[cfg(not(feature = "homework"))]
            println!("Compilation failed {e}");

            print_timings();

            return;
        }
    };

    #[cfg(feature = "measure")]
    if measure_repeat > 0 {
        for _ in 0..reps {
            let _ = std::hint::black_box(lex::LexLinear::lex(&file));
        }
    }

    if !parse {
        if !quiet {
            use std::io::Write;

            let output = {
                measure!("out");
                use std::fmt::Write;
                let mut output = String::new();

                for token in &tokens {
                    token.fmt(&mut output, &string_map).unwrap();
                    output.push('\n');
                }
                writeln!(output, "Compilation succeeded").unwrap();

                output
            };

            measure!("write output");
            stdout().write_all(output.as_bytes()).unwrap();
        }

        print_timings();

        exit(0);
    }

    let parsed = match parse::parse(&tokens, &input_by_token, &string_map, &file, &path) {
        Ok(tokens) => tokens,
        #[allow(unused_variables)]
        Err(e) => {
            #[cfg(feature = "homework")]
            println!("Compilation failed");
            #[cfg(not(feature = "homework"))]
            println!("Compilation failed {e}");

            print_timings();

            return;
        }
    };

    #[cfg(feature = "measure")]
    if measure_repeat > 0 {
        for _ in 0..reps {
            let _ = std::hint::black_box(parse::parse(&tokens, &input_by_token, &file, &path));
        }
    }

    if !typecheck {
        if !quiet {
            use std::io::Write;

            let output = {
                measure!("out");
                use std::fmt::Write;
                let mut output = String::new();

                for parsed in &parsed {
                    parsed.fmt(&mut output, &string_map).unwrap();
                    output.push('\n');
                }
                writeln!(output, "Compilation succeeded").unwrap();

                output
            };

            measure!("write output");
            stdout().write_all(output.as_bytes()).unwrap();
        }

        print_timings();

        exit(0);
    }

    let _ = parsed;
}
