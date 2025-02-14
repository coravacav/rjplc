#![deny(clippy::pedantic)]

use std::{io::stdout, path::PathBuf, process::exit};

use clap::{ArgGroup, Parser};
use measure::print_timings;
use rjplc::{lex, measure, parse, typecheck, CustomDisplay};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
#[allow(clippy::struct_excessive_bools)]
#[clap(group(
    ArgGroup::new("required_args")
        .required(true)
        .args(&["lex", "parse", "typecheck"])
))]
struct Args {
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
}

#[allow(clippy::too_many_lines)]
fn main() {
    #[allow(unused_mut)]
    let args = Args::parse();

    let file = unwrap_or_exit(std::fs::read_to_string(&args.path));

    let (tokens, string_map) = unwrap_or_exit(lex::lex(&file));

    if !args.parse && !args.typecheck {
        print_output(args.quiet, &tokens, &string_map, true);
    }

    let (mut cmds, tokens_consumed) =
        unwrap_or_exit(parse::parse(&tokens, &string_map, &file, &args.path));

    if args.typecheck {
        unwrap_or_exit(typecheck::typecheck(
            &mut cmds,
            &string_map,
            &tokens_consumed,
        ));
    }

    print_output(args.quiet, &cmds, &string_map, true);
}

fn generate_output<T: CustomDisplay>(
    items: &[T],
    string_map: &[&str],
    add_compilation_succeeded: bool,
) -> String {
    measure!("out");
    use std::fmt::Write;
    let mut output = String::new();

    for item in items {
        item.fmt(&mut output, string_map).unwrap();
        output.push('\n');
    }

    if add_compilation_succeeded {
        writeln!(output, "Compilation succeeded").unwrap();
    }

    output
}

fn print_output<T: CustomDisplay>(
    quiet: bool,
    items: &[T],
    string_map: &[&str],
    add_compilation_succeeded: bool,
) {
    use std::io::Write;

    if !quiet {
        let output = generate_output(items, string_map, add_compilation_succeeded);
        stdout().write_all(output.as_bytes()).unwrap();
    }
}

fn unwrap_or_exit<T, E: std::fmt::Display>(result: std::result::Result<T, E>) -> T {
    match result {
        Ok(t) => t,
        Err(e) => {
            #[cfg(feature = "homework")]
            println!("Compilation failed");
            #[cfg(not(feature = "homework"))]
            println!("Compilation failed {e}");

            print_timings();
            exit(1);
        }
    }
}
