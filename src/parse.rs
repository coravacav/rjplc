use color_eyre::eyre::Result;

use crate::lex::{Op, Token};

#[cfg(test)]
use crate::{test_correct, test_solos};

trait Consume<'a, 'b>: Sized {
    fn consume_maybe(tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Self)>;
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub struct Variable<'a>(&'a str);

impl std::fmt::Display for Variable<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'a, 'b> Consume<'a, 'b> for Variable<'a> {
    fn consume_maybe(mut tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Self)> {
        let s = match tokens.first()? {
            Token::VARIABLE(s) => s,
            _ => return None,
        };

        tokens.skip_one();
        Some((tokens, Self(s)))
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub struct LiteralString<'a>(&'a str);

impl std::fmt::Display for LiteralString<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
}

impl<'a, 'b> Consume<'a, 'b> for LiteralString<'a> {
    fn consume_maybe(mut tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Self)> {
        let s = match tokens.first()? {
            Token::STRING(s) => s,
            _ => return None,
        };

        tokens.skip_one();
        Some((tokens, Self(s)))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Cmd<'a> {
    Read(LiteralString<'a>, LValue<'a>),
    Write(Expr<'a>, LiteralString<'a>),
    Let(LValue<'a>, Expr<'a>),
    Assert(Expr<'a>, LiteralString<'a>),
    Print(LiteralString<'a>),
    Show(Expr<'a>),
    Time(Box<Cmd<'a>>),
    Fn(Variable<'a>, Vec<Binding<'a>>, Type<'a>, Vec<Statement<'a>>),
    Type(Variable<'a>, Type<'a>),
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
                let (mut tokens, s) = LiteralString::consume_maybe(tokens)?;
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
                let (mut tokens, s) = LiteralString::consume_maybe(tokens)?;
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
                let (mut tokens, s) = LiteralString::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Write(expr, s)))
            }
            Token::PRINT => {
                let (mut tokens, s) = LiteralString::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Print(s)))
            }
            Token::FN => {
                let (mut tokens, v) = Variable::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::LPAREN)?;
                let (mut tokens, bindings) = consume_list(tokens, Token::RPAREN, Token::COMMA)?;
                tokens.check_one_then_skip(Token::COLON)?;
                let (mut tokens, ty) = Type::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::LCURLY)?;
                tokens.check_one_then_skip(Token::NEWLINE)?;
                let (tokens, statements) = consume_list(tokens, Token::RCURLY, Token::NEWLINE)?;
                Some((tokens, Self::Fn(v, bindings, ty, statements)))
            }
            Token::TYPE => {
                let (mut tokens, v) = Variable::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::EQUALS)?;
                dbg!(tokens);
                let (mut tokens, ty) = Type::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Type(v, ty)))
            }
            _ => None,
        }
    }
}

impl std::fmt::Display for Cmd<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Cmd::Read(file, lvalue) => write!(f, "(ReadCmd {file} {lvalue})"),
            Cmd::Write(expr, file) => write!(f, "(WriteCmd {expr} {file})"),
            Cmd::Let(lvalue, expr) => write!(f, "(LetCmd {lvalue} {expr})"),
            Cmd::Assert(expr, msg) => write!(f, "(AssertCmd {expr} {msg})"),
            Cmd::Print(msg) => write!(f, "(PrintCmd {msg})"),
            Cmd::Show(expr) => write!(f, "(ShowCmd {expr})"),
            Cmd::Time(cmd) => write!(f, "(TimeCmd {cmd})"),
            Cmd::Fn(name, bindings, ty, statements) => {
                write!(f, "(FnCmd {name} (")?;
                // I hate this.
                for (i, binding) in bindings.iter().enumerate() {
                    if i != 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{binding}")?;
                }
                write!(f, ") {ty}")?;
                for statement in statements.iter() {
                    write!(f, " {statement}")?;
                }
                write!(f, ")")
            }
            Cmd::Type(name, ty) => {
                write!(f, "(TypeCmd {name} {ty})")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement<'a> {
    Let(LValue<'a>, Expr<'a>),
    Assert(Expr<'a>, LiteralString<'a>),
    Return(Expr<'a>),
}

impl std::fmt::Display for Statement<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Let(lvalue, expr) => write!(f, "(LetStmt {lvalue} {expr})"),
            Statement::Assert(expr, msg) => write!(f, "(AssertStmt {expr} {msg})"),
            Statement::Return(expr) => write!(f, "(ReturnStmt {expr})"),
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Statement<'a> {
    fn consume_maybe(mut tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Self)> {
        match tokens.first()? {
            Token::ASSERT => {
                tokens.skip_one();
                let (mut tokens, expr) = Expr::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::COMMA)?;
                let (mut tokens, msg) = LiteralString::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Assert(expr, msg)))
            }
            Token::RETURN => {
                tokens.skip_one();
                let (mut tokens, expr) = Expr::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Return(expr)))
            }
            Token::LET => {
                tokens.skip_one();
                let (mut tokens, lvalue) = LValue::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::EQUALS)?;
                let (mut tokens, expr) = Expr::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::NEWLINE)?;
                Some((tokens, Self::Let(lvalue, expr)))
            }
            _ => None,
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
    Tuple(Vec<Expr<'a>>),
    ArrayIndex(Box<Expr<'a>>, Vec<Expr<'a>>),
    Binop(Box<Expr<'a>>, Op, Box<Expr<'a>>),
    Call(Variable<'a>, Vec<Expr<'a>>),
    TupleIndex(Box<Expr<'a>>, Vec<Expr<'a>>),
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
            Expr::Tuple(exprs) => {
                write!(f, "(TupleLiteralExpr")?;
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
            Expr::TupleIndex(s, exprs) => {
                write!(f, "(TupleIndexExpr")?;
                write!(f, " {s}")?;
                for expr in exprs.iter() {
                    match expr {
                        Expr::Int(i) => write!(f, " {i}")?,
                        _ => write!(f, " {expr}")?,
                    }
                }
                write!(f, ")")
            }
            Expr::Binop(expr, op, expr2) => {
                write!(f, "(BinopExpr {expr} {op} {expr2})")
            }
            Expr::Call(expr, exprs) => {
                write!(f, "(CallExpr {expr}")?;
                for expr in exprs.iter() {
                    write!(f, " {expr}")?;
                }
                write!(f, ")")
            }
        }
    }
}

fn consume_list<'a, 'b, T: Consume<'a, 'b>>(
    mut tokens: &'b [Token<'a>],
    end_token: Token<'a>,
    delimeter: Token<'a>,
) -> Option<(&'b [Token<'a>], Vec<T>)> {
    let mut list = vec![];
    loop {
        if tokens.check_one_then_skip(end_token).is_some() {
            break;
        }

        let (rem_tokens, t) = T::consume_maybe(tokens)?;
        if tokens == rem_tokens {
            return None;
        }

        tokens = rem_tokens;
        list.push(t);
        if tokens.check_one_then_skip(delimeter).is_none()
            && tokens.check_one_then_skip(end_token).is_some()
        {
            break;
        };
    }

    Some((tokens, list))
}

// fn consume_comma_expr_list<'a, 'b>(
//     mut tokens: &'b [Token<'a>],
//     end_token: Token,
// ) -> Option<(&'b [Token<'a>], Vec<Expr<'a>>)> {
//     let mut exprs = vec![];
//     loop {
//         if tokens.check_one_then_skip(end_token).is_some() {
//             break;
//         }

//         let (rem_tokens, expr) = Expr::consume_maybe(tokens)?;
//         tokens = rem_tokens;
//         exprs.push(expr);
//         if tokens.check_one_then_skip(Token::COMMA).is_none()
//             && tokens.check_one_then_skip(end_token).is_some()
//         {
//             break;
//         };
//     }

//     Some((tokens, exprs))
// }

impl<'a, 'b> Consume<'a, 'b> for Expr<'a> {
    fn consume_maybe(mut tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Expr<'a>)> {
        let (mut tokens, mut expr) = match tokens.first()? {
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

                let (tokens, exprs) = consume_list(tokens, Token::RSQUARE, Token::COMMA)?;

                // intentionally early
                return Some((tokens, Expr::Array(exprs)));
            }
            Token::LPAREN => {
                tokens.skip_one();
                let (mut tokens, expr) = Expr::consume_maybe(tokens)?;
                tokens.check_one_then_skip(Token::RPAREN)?;
                (tokens, expr)
            }
            Token::LCURLY => {
                tokens.skip_one();
                let (tokens, exprs) = consume_list(tokens, Token::RCURLY, Token::COMMA)?;
                (tokens, Expr::Tuple(exprs))
            }
            _ => return None,
        };

        let (mut tokens, expr) = loop {
            match (tokens.first(), &expr) {
                (Some(Token::LSQUARE), _) => {
                    tokens.skip_one();
                    let (rem_tokens, exprs) = consume_list(tokens, Token::RSQUARE, Token::COMMA)?;
                    tokens = rem_tokens;
                    expr = Expr::ArrayIndex(Box::new(expr), exprs)
                }
                (Some(Token::LPAREN), Expr::Variable(s)) => {
                    let s = Variable(s);
                    tokens.skip_one();
                    let (rem_tokens, exprs) = consume_list(tokens, Token::RPAREN, Token::COMMA)?;
                    tokens = rem_tokens;
                    expr = Expr::Call(s, exprs)
                }
                (Some(Token::LCURLY), _) => {
                    tokens.skip_one();
                    let (rem_tokens, exprs) = consume_list(tokens, Token::RCURLY, Token::COMMA)?;
                    tokens = rem_tokens;
                    expr = Expr::TupleIndex(Box::new(expr), exprs)
                }
                _ => break (tokens, expr),
            };
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

#[derive(Debug, Clone, PartialEq)]
pub enum LValue<'a> {
    Var(Variable<'a>),
    Arg(Argument<'a>),
    Tuple(Vec<LValue<'a>>),
}

impl std::fmt::Display for LValue<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LValue::Var(s) => write!(f, "(VarLValue {s})"),
            LValue::Arg(s) => write!(f, "(ArgLValue {s})"),
            LValue::Tuple(lvs) => {
                write!(f, "(TupleLValue")?;
                for lv in lvs.iter() {
                    write!(f, " {lv}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for LValue<'a> {
    fn consume_maybe(mut tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Self)> {
        if let Some((tokens, arg)) = Argument::consume_maybe(tokens) {
            return match arg {
                // This is really weird hw3 special casing.
                Argument::Var(s) => Some((tokens, LValue::Var(s))),
                _ => Some((tokens, LValue::Arg(arg))),
            };
        }

        match tokens.first()? {
            Token::VARIABLE(s) => {
                tokens.skip_one();
                Some((tokens, LValue::Var(Variable(s))))
            }
            Token::LCURLY => {
                tokens.skip_one();
                let (tokens, lvs) = consume_list(tokens, Token::RCURLY, Token::COMMA)?;
                Some((tokens, LValue::Tuple(lvs)))
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type<'a> {
    Var(&'a str),
    Array(Box<Type<'a>>, u8),
    Float,
    Tuple(Vec<Type<'a>>),
}

impl std::fmt::Display for Type<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Var(s) => write!(f, "(VarType {s})"),
            Type::Array(s, i) => write!(f, "(ArrayType {s} {i})"),
            Type::Float => write!(f, "(FloatType)"),
            Type::Tuple(tys) => {
                write!(f, "(TupleType")?;
                for ty in tys.iter() {
                    write!(f, " {ty}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Type<'a> {
    fn consume_maybe(mut tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Self)> {
        dbg!(tokens);
        let (mut tokens, ty) = match tokens.first()? {
            Token::VARIABLE(s) => {
                tokens.skip_one();
                (tokens, Type::Var(s))
            }
            Token::FLOAT => {
                tokens.skip_one();
                (tokens, Type::Float)
            }
            Token::LCURLY => {
                tokens.skip_one();
                let (tokens, tys) = consume_list(tokens, Token::RCURLY, Token::COMMA)?;
                (tokens, Type::Tuple(tys))
            }
            _ => return None,
        };

        let (tokens, ty) = if tokens.check_one_then_skip(Token::LSQUARE).is_some() {
            let mut depth: u8 = 1;
            loop {
                match tokens.next_and_skip()? {
                    Token::RSQUARE => {
                        break (tokens, Self::Array(Box::new(ty), depth));
                    }
                    Token::COMMA => {
                        depth += 1;
                    }
                    _ => return None,
                }
            }
        } else {
            (tokens, ty)
        };

        Some((tokens, ty))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Binding<'a> {
    Var(Argument<'a>, Type<'a>),
}

impl std::fmt::Display for Binding<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Binding::Var(s, ty) => write!(f, "(VarBinding {s} {ty})"),
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Binding<'a> {
    fn consume_maybe(tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Self)> {
        let (mut tokens, arg) = Argument::consume_maybe(tokens)?;
        tokens.check_one_then_skip(Token::COLON)?;
        let (tokens, ty) = Type::consume_maybe(tokens)?;
        Some((tokens, Self::Var(arg, ty)))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Argument<'a> {
    Var(Variable<'a>),
    Array(Variable<'a>, Vec<Variable<'a>>),
}

impl std::fmt::Display for Argument<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Argument::Var(s) => write!(f, "(VarArgument {s})"),
            Argument::Array(s, args) => {
                write!(f, "(ArrayArgument {s}")?;
                for arg in args.iter() {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Argument<'a> {
    fn consume_maybe(tokens: &'b [Token<'a>]) -> Option<(&'b [Token<'a>], Self)> {
        let (mut tokens, s) = Variable::consume_maybe(tokens)?;

        if tokens.check_one_then_skip(Token::LSQUARE).is_some() {
            let (tokens, args) = consume_list(tokens, Token::RSQUARE, Token::COMMA)?;
            Some((tokens, Self::Array(s, args)))
        } else {
            Some((tokens, Self::Var(s)))
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
fn test_parse_correct() {
    use regex::Regex;
    let regex = Regex::new(r"\n\s+").unwrap();

    let tester = |file: &str, solution_file: &str| {
        let parsed = match parse(&crate::lex::lex(file).expect("Lexing should work")) {
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
            let solution_file = regex.replace_all(solution_file, " ");
            pretty_assertions::assert_eq!(output, solution_file);
        } else {
            pretty_assertions::assert_eq!(output, solution_file);
        }
    };

    test_correct("grader/hw3/ok", tester);
    test_correct("grader/hw3/ok-fuzzer", tester);
    test_correct("grader/hw4/ok", tester);
}

#[test]
fn test_parse_fails() {
    let tester = |file: Option<&str>| {
        let Ok(tokens) = crate::lex::lex(file.unwrap()) else {
            return;
        };

        assert!(parse(&tokens).is_err());
    };

    test_solos("grader/hw3/fail-fuzzer1", tester);
    test_solos("grader/hw3/fail-fuzzer2", tester);
    test_solos("grader/hw3/fail-fuzzer3", tester);
}
