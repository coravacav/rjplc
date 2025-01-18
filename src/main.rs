mod lex;

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

    if lex {
        let file = match std::fs::read_to_string(&path) {
            Ok(file) => file,
            Err(e) => {
                println!("Compilation failed {e}");
                return;
            }
        };

        let tokens = match lex::lex(&file) {
            Ok(tokens) => tokens,
            Err(e) => {
                println!("Compilation failed {e:?}");
                return;
            }
        };

        if !parse {
            for token in tokens {
                println!("{}", token);
            }
        }
    }

    println!("Compilation succeeded")
}
