use color_eyre::eyre::Result;

use crate::lex::{Op, Token};

trait Consume<'a, 'b>: Sized {
    fn consume_maybe(tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Self)>;
}

#[derive(Debug, Clone, PartialEq)]
pub enum Cmd<'a> {
    Read(&'a str, LValue<'a>),
    Write(Expr<'a>, &'a str),
    Let(LValue<'a>, Expr<'a>),
    Assert(Expr<'a>, &'a str),
    Print(&'a str),
    Show(Expr<'a>),
    Time(Box<Cmd<'a>>),
}

trait ParserHelper {
    fn skip_one(&mut self);
    fn next_and_skip(&mut self) -> Option<&Token<'_>>;
    fn check_one_then_skip(&mut self, token: Token<'_>) -> Option<()>;
    fn check_one(&self, token: Token<'_>) -> bool;
}

impl ParserHelper for &[Token<'_>] {
    fn skip_one(&mut self) {
        *self = &self[1..]
    }

    fn next_and_skip(&mut self) -> Option<&Token<'_>> {
        let next = self.first();
        self.skip_one();
        next
    }

    fn check_one_then_skip(&mut self, token: Token<'_>) -> Option<()> {
        if self.check_one(token) {
            self.skip_one();
            Some(())
        } else {
            None
        }
    }

    fn check_one(&self, token: Token<'_>) -> bool {
        self.first() == Some(&token)
    }
}

impl<'a, 'b> Consume<'a, 'b> for Cmd<'a> {
    fn consume_maybe(mut tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Self)> {
        match tokens.next_and_skip()? {
            Token::READ => {
                tokens.check_one_then_skip(Token::IMAGE)?;
                let s = if let Token::STRING(s) = tokens.first()? {
                    tokens.skip_one();
                    s
                } else {
                    return None;
                };
                tokens.check_one_then_skip(Token::TO)?;
                let (mut tokens, lvalue) = LValue::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Read(s, lvalue)))
            }
            Token::TIME => {
                let (tokens, cmd) = Cmd::consume_maybe(tokens)?;
                Some((tokens, Self::Time(Box::new(cmd))))
            }
            Token::LET => {
                let (mut tokens, lvalue) = LValue::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::EQUALS)?;
                let (mut tokens, expr) = Expr::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Let(lvalue, expr)))
            }
            Token::ASSERT => {
                let (mut tokens, expr) = Expr::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::COMMA)?;
                let s = if let Token::STRING(s) = tokens.first()? {
                    tokens.skip_one();
                    s
                } else {
                    return None;
                };
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Assert(expr, s)))
            }
            Token::SHOW => {
                let (mut tokens, expr) = Expr::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Show(expr)))
            }
            Token::WRITE => {
                tokens.check_one_then_skip(Token::IMAGE)?;
                let (mut tokens, expr) = Expr::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::TO)?;
                let s = if let Token::STRING(s) = tokens.first()? {
                    tokens.skip_one();
                    s
                } else {
                    return None;
                };
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Write(expr, s)))
            }
            Token::PRINT => {
                let s = if let Token::STRING(s) = tokens.first()? {
                    tokens.skip_one();
                    s
                } else {
                    return None;
                };
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Print(s)))
            }
            _ => None,
        }
    }
}

impl std::fmt::Display for Cmd<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Cmd::Read(file, lvalue) => write!(f, "(ReadCmd \"{file}\" {lvalue})"),
            Cmd::Write(expr, file) => write!(f, "(WriteCmd {expr} \"{file}\")"),
            Cmd::Let(lvalue, expr) => write!(f, "(LetCmd {lvalue} {expr})"),
            Cmd::Assert(expr, msg) => write!(f, "(AssertCmd {expr} \"{msg}\")"),
            Cmd::Print(msg) => write!(f, "(PrintCmd \"{msg}\")"),
            Cmd::Show(expr) => write!(f, "(ShowCmd {expr})"),
            Cmd::Time(cmd) => write!(f, "(TimeCmd {cmd})"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<'a> {
    Int(i64),
    Float(f64),
    True,
    False,
    Variable(&'a str),
    Array(Vec<Expr<'a>>),
    ArrayIndex(Box<Expr<'a>>, Vec<Expr<'a>>),
    Binop(Box<Expr<'a>>, Op, Box<Expr<'a>>),
}

impl std::fmt::Display for Expr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Int(i) => write!(f, "(IntExpr {i})"),
            Expr::Float(fl) => write!(f, "(FloatExpr {:.0})", fl.trunc()),
            Expr::True => write!(f, "(TrueExpr)"),
            Expr::False => write!(f, "(FalseExpr)"),
            Expr::Variable(s) => write!(f, "(VarExpr {s})"),
            Expr::Array(exprs) => {
                write!(f, "(ArrayLiteralExpr")?;
                for expr in exprs.iter() {
                    write!(f, " {expr}")?;
                }
                write!(f, ")")
            }
            Expr::ArrayIndex(s, exprs) => {
                write!(f, "(ArrayIndexExpr")?;
                write!(f, " {s}")?;
                for expr in exprs.iter() {
                    write!(f, " {expr}")?;
                }
                write!(f, ")")
            }
            Expr::Binop(expr, op, expr2) => {
                write!(f, "(BinopExpr {expr} {op} {expr2})")
            }
        }
    }
}

fn consume_maybe_array_contents<'a, 'b>(
    mut tokens: &'b [Token<'a>],
) -> Option<(&'b [Token<'a>], Vec<Expr<'a>>)> {
    let mut exprs = vec![];
    loop {
        if tokens.check_one_then_skip(Token::RSQUARE).is_some() {
            break;
        }

        let (skipped_tokens, expr) = Expr::consume_maybe(tokens)?;
        tokens = skipped_tokens;
        exprs.push(expr);
        if tokens.check_one_then_skip(Token::COMMA).is_none()
            && tokens.check_one_then_skip(Token::RSQUARE).is_some()
        {
            break;
        };
    }

    Some((tokens, exprs))
}

impl<'a, 'b> Consume<'a, 'b> for Expr<'a> {
    fn consume_maybe(mut tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Expr<'a>)> {
        let (mut tokens, expr) = match tokens.first()? {
            Token::INTVAL(s) => {
                tokens.skip_one();
                (tokens, Expr::Int(s.parse().ok()?))
            }
            Token::FLOATVAL(s) => {
                tokens.skip_one();
                (
                    tokens,
                    Expr::Float(s.parse().ok().filter(|f: &f64| f.is_finite())?),
                )
            }
            Token::TRUE => {
                tokens.skip_one();
                (tokens, Expr::True)
            }
            Token::FALSE => {
                tokens.skip_one();
                (tokens, Expr::False)
            }
            Token::VARIABLE(s) => {
                tokens.skip_one();
                (tokens, Expr::Variable(s))
            }
            Token::LSQUARE => {
                tokens.skip_one();

                let (tokens, exprs) = consume_maybe_array_contents(tokens)?;

                // intentionally early
                return Some((tokens, Expr::Array(exprs)));
            }
            _ => return None,
        };

        let (mut tokens, expr) = if tokens.check_one_then_skip(Token::LSQUARE).is_some() {
            let (tokens, exprs) = consume_maybe_array_contents(tokens)?;
            (tokens, Expr::ArrayIndex(Box::new(expr), exprs))
        } else {
            (tokens, expr)
        };

        let (tokens, expr) = match tokens.first()? {
            Token::OP(c @ Op::Eq) => {
                tokens.skip_one();
                let (tokens, expr2) = Expr::consume_maybe(tokens)?;
                (tokens, Expr::Binop(Box::new(expr), *c, Box::new(expr2)))
            }
            _ => (tokens, expr),
        };

        Some((tokens, expr))
    }
}

/// Always a variable
#[derive(Debug, Clone, PartialEq)]
pub struct LValue<'a>(&'a str);

impl std::fmt::Display for LValue<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(VarLValue {})", self.0)
    }
}

impl<'a, 'b> Consume<'a, 'b> for LValue<'a> {
    fn consume_maybe(mut tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Self)> {
        if let Token::VARIABLE(s) = tokens.first()? {
            tokens.skip_one();
            Some((tokens, Self(s)))
        } else {
            None
        }
    }
}

pub fn parse<'a>(mut tokens: &[Token<'a>]) -> Result<Vec<Cmd<'a>>> {
    let mut cmds = vec![];

    while !tokens.is_empty() {
        if let Some((moved_tokens, cmd)) = Cmd::consume_maybe(tokens) {
            assert_ne!(moved_tokens, tokens);
            tokens = moved_tokens;
            cmds.push(cmd);
        } else if let Some(Token::NEWLINE) = tokens.first() {
            tokens.skip_one();
        } else if !matches!(&tokens, [Token::END_OF_FILE]) {
            #[cfg(test)]
            for token in tokens {
                println!("{token}");
            }

            color_eyre::eyre::bail!("Expected EOF");
        } else {
            break;
        }
    }

    Ok(cmds)
}

#[test]
fn test_parse_correct_ok() {
    use std::{fs, path::Path};
    let folder = Path::new("grader/hw3/ok");
    if !folder.exists() {
        panic!("Could not find {}", folder.display());
    }

    use regex::Regex;
    let regex = Regex::new(r"\n\s+").unwrap();

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

        let parsed = match parse(&crate::lex::lex(&file).expect("Lexing should work")) {
            Ok(parsed) => parsed,
            Err(e) => {
                panic!("Compilation failed {e}");
            }
        };

        let mut output = String::new();

        for parsed in parsed {
            use std::fmt::Write;
            writeln!(output, "{}", parsed).unwrap();
        }

        if output != solution_file {
            let output = regex.replace_all(&output, " ");
            let solution_file = regex.replace_all(&solution_file, " ");
            pretty_assertions::assert_eq!(output, solution_file);
        } else {
            pretty_assertions::assert_eq!(output, solution_file);
        }
    }
}

#[test]
fn test_parse_correct_ok_fuzzer() {
    use std::{fs, path::Path};
    let folder = Path::new("grader/hw3/ok-fuzzer");
    if !folder.exists() {
        panic!("Could not find {}", folder.display());
    }

    use regex::Regex;
    let regex = Regex::new(r"\n\s+").unwrap();

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

        let parsed = match parse(&crate::lex::lex(&file).expect("Lexing should work")) {
            Ok(parsed) => parsed,
            Err(e) => {
                panic!("Compilation failed {e}");
            }
        };

        let mut output = String::new();

        for parsed in parsed {
            use std::fmt::Write;
            writeln!(output, "{}", parsed).unwrap();
        }

        if output != solution_file {
            let output = regex.replace_all(&output, " ");
            let solution_file = regex.replace_all(&solution_file, " ");
            pretty_assertions::assert_eq!(output, solution_file);
        } else {
            pretty_assertions::assert_eq!(output, solution_file);
        }
    }
}

#[test]
fn test_lex_fails_1() {
    use std::{fs, path::Path};
    let folder = Path::new("grader/hw3/fail-fuzzer1");
    if !folder.exists() {
        panic!("Could not find {}", folder.display());
    }

    let test_paths = fs::read_dir(folder)
        .unwrap()
        .flatten()
        .filter(|f| f.file_type().unwrap().is_file())
        .filter(|f| f.path().extension().unwrap() == "jpl");

    for test_path in test_paths {
        let file = fs::read_to_string(dbg!(test_path.path())).unwrap();
        let tokens = crate::lex::lex(&file).unwrap();

        assert!(parse(&tokens).is_err());
    }
}

#[test]
fn test_lex_fails_2() {
    use std::{fs, path::Path};
    let folder = Path::new("grader/hw3/fail-fuzzer2");
    if !folder.exists() {
        panic!("Could not find {}", folder.display());
    }

    let test_paths = fs::read_dir(folder)
        .unwrap()
        .flatten()
        .filter(|f| f.file_type().unwrap().is_file())
        .filter(|f| f.path().extension().unwrap() == "jpl");

    for test_path in test_paths {
        let file = fs::read_to_string(dbg!(test_path.path())).unwrap();
        let tokens = crate::lex::lex(&file).unwrap();

        assert!(parse(&tokens).is_err());
    }
}

#[test]
fn test_lex_fails_3() {
    use std::{fs, path::Path};
    let folder = Path::new("grader/hw3/fail-fuzzer3");
    if !folder.exists() {
        panic!("Could not find {}", folder.display());
    }

    let test_paths = fs::read_dir(folder)
        .unwrap()
        .flatten()
        .filter(|f| f.file_type().unwrap().is_file())
        .filter(|f| f.path().extension().unwrap() == "jpl");

    for test_path in test_paths {
        let file = fs::read_to_string(dbg!(test_path.path())).unwrap();
        let Ok(tokens) = crate::lex::lex(&file) else {
            continue;
        };

        assert!(parse(&tokens).is_err());
    }
}
