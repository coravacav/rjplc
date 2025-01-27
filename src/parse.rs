use std::{cell::Cell, rc::Rc};

use color_eyre::eyre::{bail, eyre, Context, OptionExt, Result};
use colored::Colorize;
use itertools::Itertools;

use crate::{
    lex::{Op, Token},
    undo_slice_by_cuts, UndoSliceSelection,
};

#[cfg(test)]
use crate::{test_correct, test_solos};

trait Consume<'a>: Sized {
    fn consume(tokens: Parser<'a>) -> Result<(Parser<'a>, Self)>;
    #[allow(dead_code)]
    fn get_name(&self) -> &'static str;
}

trait PrintJoined {
    fn print_joined(&self, sep: &str) -> Result<String>;
}

impl<T: std::fmt::Display + std::fmt::Debug> PrintJoined for [T] {
    fn print_joined(&self, sep: &str) -> Result<String> {
        use std::fmt::Write;
        let mut s = String::new();
        for (i, t) in self.iter().enumerate() {
            if i != 0 {
                write!(s, "{sep}")?;
            }
            write!(s, "{t}")?;
        }

        Ok(s)
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Parser<'a> {
    original_tokens: &'a [Token<'a>],
    current_position: Cell<usize>,
    input_by_token: &'a [&'a str],
    successfully_parsed: Rc<Cell<usize>>,
    source: &'a str,
}

impl<'a> Parser<'a> {
    fn skip_one(&self) {
        self.current_position.set(self.current_position.get() + 1);
        self.successfully_parsed
            .set(self.successfully_parsed.get() + 1);
    }

    fn next_and_skip(&self) -> Result<Token<'a>> {
        let next = self.first();
        self.skip_one();
        next.ok_or_eyre("Unexpected end of tokens")
    }

    fn check_skip(&self, token: Token<'a>) -> Result<()> {
        if self.check_one(token) {
            self.skip_one();
            Ok(())
        } else {
            Err(eyre!("expected {token:?}, found {:?}", self.first()))
        }
    }

    fn check_one(&self, token: Token<'a>) -> bool {
        self.first() == Some(token)
    }

    fn first(&self) -> Option<Token<'a>> {
        self.original_tokens
            .get(self.current_position.get())
            .copied()
    }

    fn next(&self) -> Option<Token<'a>> {
        let next = self.first();
        self.skip_one();
        next
    }

    fn is_empty(&self) -> bool {
        self.current_position.get() == self.original_tokens.len()
    }

    /// This function prints the error token text in red and the surrounding text.
    fn print_error(&self) {
        let current_position = self.current_position.get();
        let error_position = current_position + self.successfully_parsed.get();

        let [source_pre, semi_valid, error, source_post] = undo_slice_by_cuts(
            self.source,
            [
                UndoSliceSelection::Boundless,
                UndoSliceSelection::Beginning(self.input_by_token[current_position]),
                UndoSliceSelection::Beginning(self.input_by_token[error_position]),
                UndoSliceSelection::End(self.input_by_token[error_position]),
                UndoSliceSelection::Boundless,
            ],
        );

        let (source_pre, newlines, newline_padding) = {
            let mut src_iter = source_pre.split('\n').rev();

            let source_pre = src_iter
                .by_ref()
                .take(2)
                .map(|line| line.dimmed().to_string())
                .collect_vec()
                .iter()
                .rev()
                .join("\n");

            let lines_before = src_iter.count();

            (
                source_pre,
                lines_before..,
                lines_before.to_string().len() + 1,
            )
        };

        let semi_valid = semi_valid
            .split('\n')
            .map(|line| line.green().dimmed().to_string())
            .join("\n");

        let error = error
            .split('\n')
            .map(|line| line.red().to_string())
            .join("\n");

        let source_post = source_post
            .split('\n')
            .take(2)
            .map(|line| line.dimmed().to_string())
            .join("\n");

        let output = format!("{}{}{}{}", source_pre, semi_valid, error, source_post)
            .split('\n')
            .zip(newlines)
            .fold(String::new(), |acc, (line, newline_count)| {
                format!(
                    "{acc}{}{line}\n",
                    format!("{newline_count:newline_padding$} | ").bright_blue()
                )
            });

        println!("{}", output);
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub struct Variable<'a>(&'a str);

impl std::fmt::Display for Variable<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'a> Consume<'a> for Variable<'a> {
    fn consume(tokens: Parser<'a>) -> Result<(Parser<'a>, Self)> {
        let s = match tokens.next() {
            Some(Token::VARIABLE(s)) => s,
            Some(t) => bail!("expected variable, found {t:?}"),
            None => bail!("expected a variable, unexpected end of tokens"),
        };

        Ok((tokens, Self(s)))
    }

    fn get_name(&self) -> &'static str {
        "variable"
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub struct LiteralString<'a>(&'a str);

impl std::fmt::Display for LiteralString<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
}

impl<'a> Consume<'a> for LiteralString<'a> {
    fn consume(tokens: Parser<'a>) -> Result<(Parser<'a>, Self)> {
        let s = match tokens.first() {
            Some(Token::STRING(s)) => s,
            Some(t) => bail!("expected string, found {t:?}"),
            None => bail!("expected a string, unexpected end of tokens"),
        };

        tokens.skip_one();
        Ok((tokens, Self(s)))
    }

    fn get_name(&self) -> &'static str {
        "string literal"
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field<'a>(Variable<'a>, Type<'a>);

impl std::fmt::Display for Field<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.0, self.1)
    }
}

impl<'a> Consume<'a> for Field<'a> {
    fn consume(tokens: Parser<'a>) -> Result<(Parser<'a>, Self)> {
        let (tokens, s) = Variable::consume(tokens).wrap_err("parsing field")?;
        tokens.check_skip(Token::COLON).wrap_err("parsing field")?;
        let (tokens, ty) = Type::consume(tokens).wrap_err("parsing field")?;
        Ok((tokens, Self(s, ty)))
    }

    fn get_name(&self) -> &'static str {
        "field"
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
    Struct(Variable<'a>, Vec<Field<'a>>),
}

impl<'a> Consume<'a> for Cmd<'a> {
    fn consume(tokens: Parser<'a>) -> Result<(Parser<'a>, Self)> {
        match tokens.next_and_skip()? {
            Token::READ => {
                tokens.check_skip(Token::IMAGE).wrap_err("parsing read command")?;
                let (tokens, s) = LiteralString::consume(tokens).wrap_err("parsing read command")?;
                tokens.check_skip(Token::TO).wrap_err("parsing read command")?;
                let (tokens, lvalue) = LValue::consume(tokens).wrap_err("parsing read command")?;
                tokens.check_skip(Token::NEWLINE).wrap_err("parsing read command")?;
                Ok((tokens, Self::Read(s, lvalue)))
            }
            Token::TIME => {
                let (tokens, cmd) = Cmd::consume(tokens).wrap_err("parsing time command")?;
                Ok((tokens, Self::Time(Box::new(cmd))))
            }
            Token::LET => {
                let (tokens, lvalue) = LValue::consume(tokens).wrap_err("parsing let command")?;
                tokens.check_skip(Token::EQUALS).wrap_err("parsing let command")?;
                let (tokens, expr) = Expr::consume(tokens).wrap_err("parsing let command")?;
                tokens.check_skip(Token::NEWLINE).wrap_err("parsing let command")?;
                Ok((tokens, Self::Let(lvalue, expr)))
            }
            Token::ASSERT => {
                let (tokens, expr) = Expr::consume(tokens).wrap_err("parsing assert command")?;
                tokens.check_skip(Token::COMMA).wrap_err("parsing assert command")?;
                let (tokens, s) = LiteralString::consume(tokens).wrap_err("parsing assert command")?;
                tokens.check_skip(Token::NEWLINE).wrap_err("parsing assert command")?;
                Ok((tokens, Self::Assert(expr, s)))
            }
            Token::SHOW => {
                let (tokens, expr) = Expr::consume(tokens).wrap_err("parsing show command")?;
                tokens.check_skip(Token::NEWLINE).wrap_err("parsing show command")?;
                Ok((tokens, Self::Show(expr)))
            }
            Token::WRITE => {
                tokens.check_skip(Token::IMAGE).wrap_err("parsing write command")?;
                let (tokens, expr) = Expr::consume(tokens).wrap_err("parsing write command")?;
                tokens.check_skip(Token::TO).wrap_err("parsing write command")?;
                let (tokens, s) = LiteralString::consume(tokens).wrap_err("parsing write command")?;
                tokens.check_skip(Token::NEWLINE).wrap_err("parsing write command")?;
                Ok((tokens, Self::Write(expr, s)))
            }
            Token::PRINT => {
                let (tokens, s) = LiteralString::consume(tokens).wrap_err("parsing print command")?;
                tokens.check_skip(Token::NEWLINE).wrap_err("parsing print command")?;
                Ok((tokens, Self::Print(s)))
            }
            Token::FN => {
                let (tokens, v) = Variable::consume(tokens).wrap_err("parsing fn command")?;
                tokens.check_skip(Token::LPAREN).wrap_err("parsing fn command")?;
                let (tokens, bindings) = consume_list(tokens, Token::RPAREN, Token::COMMA, false).wrap_err("parsing fn command")?;
                tokens.check_skip(Token::COLON).wrap_err("parsing fn command")?;
                let (tokens, ty) = Type::consume(tokens).wrap_err("parsing fn command")?;
                tokens.check_skip(Token::LCURLY).wrap_err("parsing fn command")?;
                tokens.check_skip(Token::NEWLINE).wrap_err("parsing fn command")?;
                let (tokens, statements) = consume_list(tokens, Token::RCURLY, Token::NEWLINE, true).wrap_err("parsing fn command")?;
                dbg!(&tokens.first());
                Ok((tokens, Self::Fn(v, bindings, ty, statements)))
            }
            Token::TYPE => {
                let (tokens, v) = Variable::consume(tokens).wrap_err("parsing type command")?;
                tokens.check_skip(Token::EQUALS).wrap_err("parsing type command")?;
                let (tokens, ty) = Type::consume(tokens).wrap_err("parsing type command")?;
                tokens.check_skip(Token::NEWLINE).wrap_err("parsing type command")?;
                Ok((tokens, Self::Type(v, ty)))
            }
            Token::STRUCT => {
                let (tokens, v) = Variable::consume(tokens).wrap_err("parsing struct command")?;
                tokens.check_skip(Token::LCURLY).wrap_err("parsing struct command")?;
                tokens
                    .check_skip(Token::NEWLINE)
                    .wrap_err("parsing struct command")?;
                let (tokens, fields) = consume_list(tokens, Token::RCURLY, Token::NEWLINE, false).wrap_err("parsing struct command")?;
                Ok((tokens, Self::Struct(v, fields)))
            }
            t => Err(eyre!("expected a command keyword (ASSERT | RETURN | LET | ASSERT | PRINT | SHOW | TIME | FN | TYPE | STRUCT), found {:?}", t)),
        }
    }

    fn get_name(&self) -> &'static str {
        "command"
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
                write!(
                    f,
                    "(FnCmd {name} (({})) {ty} {})",
                    bindings.print_joined(" ").map_err(|_| std::fmt::Error)?,
                    statements.print_joined(" ").map_err(|_| std::fmt::Error)?
                )
            }
            Cmd::Type(name, ty) => {
                write!(f, "(TypeCmd {name} {ty})")
            }
            Cmd::Struct(name, fields) => {
                write!(
                    f,
                    "(StructCmd {name}{}{})",
                    if fields.is_empty() { "" } else { " " },
                    fields.print_joined(" ").map_err(|_| std::fmt::Error)?
                )
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

impl<'a> Consume<'a> for Statement<'a> {
    fn consume(tokens: Parser<'a>) -> Result<(Parser<'a>, Self)> {
        match tokens.first() {
            Some(Token::ASSERT) => {
                tokens.skip_one();
                let (tokens, expr) = Expr::consume(tokens).wrap_err("parsing assert statement")?;
                tokens
                    .check_skip(Token::COMMA)
                    .wrap_err("parsing assert statement")?;
                let (tokens, msg) =
                    LiteralString::consume(tokens).wrap_err("parsing assert statement")?;
                Ok((tokens, Self::Assert(expr, msg)))
            }
            Some(Token::RETURN) => {
                tokens.skip_one();
                let (tokens, expr) = Expr::consume(tokens).wrap_err("parsing return statement")?;
                Ok((tokens, Self::Return(expr)))
            }
            Some(Token::LET) => {
                tokens.skip_one();
                let (tokens, lvalue) = LValue::consume(tokens).wrap_err("parsing let statement")?;
                tokens
                    .check_skip(Token::EQUALS)
                    .wrap_err("parsing let statement")?;
                let (tokens, expr) = Expr::consume(tokens).wrap_err("parsing let statement")?;
                Ok((tokens, Self::Let(lvalue, expr)))
            }
            Some(t) => Err(eyre!(
                "expected a start of statement (ASSERT | RETURN | LET), found {t:?}"
            )),
            None => Err(eyre!(
                "expected a start of statement (ASSERT | RETURN | LET), found end of tokens"
            )),
        }
    }

    fn get_name(&self) -> &'static str {
        "statement"
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<'a> {
    Int(i64),
    Float(f64),
    True,
    False,
    Void,
    Variable(&'a str),
    Array(Vec<Expr<'a>>),
    Tuple(Vec<Expr<'a>>),
    ArrayIndex(Box<Expr<'a>>, Vec<Expr<'a>>),
    #[allow(dead_code)]
    Binop(Box<Expr<'a>>, Op, Box<Expr<'a>>),
    Call(Variable<'a>, Vec<Expr<'a>>),
    TupleIndex(Box<Expr<'a>>, Vec<Expr<'a>>),
    StructLiteral(Variable<'a>, Vec<Expr<'a>>),
    Dot(Box<Expr<'a>>, Variable<'a>),
}

impl std::fmt::Display for Expr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Int(i) => write!(f, "(IntExpr {i})"),
            Expr::Float(fl) => write!(f, "(FloatExpr {:.0})", fl.trunc()),
            Expr::True => write!(f, "(TrueExpr)"),
            Expr::False => write!(f, "(FalseExpr)"),
            Expr::Void => write!(f, "(VoidExpr)"),
            Expr::Variable(s) => write!(f, "(VarExpr {s})"),
            Expr::Array(exprs) => {
                write!(
                    f,
                    "(ArrayLiteralExpr{}{})",
                    if exprs.is_empty() { "" } else { " " },
                    exprs.print_joined(" ").map_err(|_| std::fmt::Error)?
                )
            }
            Expr::Tuple(exprs) => {
                write!(
                    f,
                    "(TupleLiteralExpr {})",
                    exprs.print_joined(" ").map_err(|_| std::fmt::Error)?
                )
            }
            Expr::ArrayIndex(s, exprs) => {
                write!(
                    f,
                    "(ArrayIndexExpr {s}{}{})",
                    if exprs.is_empty() { "" } else { " " },
                    exprs.print_joined(" ").map_err(|_| std::fmt::Error)?
                )
            }
            Expr::TupleIndex(s, exprs) => {
                write!(
                    f,
                    "(TupleIndexExpr {s} {})",
                    exprs.print_joined(" ").map_err(|_| std::fmt::Error)?
                )
            }
            Expr::Binop(expr, op, expr2) => {
                write!(f, "(BinopExpr {expr} {op} {expr2})")
            }
            Expr::Call(expr, exprs) => {
                write!(
                    f,
                    "(CallExpr {expr}{}{})",
                    if exprs.is_empty() { "" } else { " " },
                    exprs.print_joined(" ").map_err(|_| std::fmt::Error)?
                )
            }
            Expr::StructLiteral(s, exprs) => {
                write!(
                    f,
                    "(StructLiteralExpr {s}{}{})",
                    if exprs.is_empty() { "" } else { " " },
                    exprs.print_joined(" ").map_err(|_| std::fmt::Error)?
                )
            }
            Expr::Dot(expr, s) => {
                write!(f, "(DotExpr {expr} {s})")
            }
        }
    }
}

fn consume_list<'a, 'b, T: Consume<'a> + std::fmt::Debug>(
    mut tokens: Parser<'a>,
    end_token: Token<'a>,
    delimeter: Token<'a>,
    delimeter_terminated: bool,
) -> Result<(Parser<'a>, Vec<T>)> {
    let mut list = vec![];
    loop {
        if tokens.check_skip(end_token).is_ok() {
            break;
        }

        let (rem_tokens, t) = T::consume(tokens.clone())?;
        if tokens == rem_tokens {
            return Err(eyre!("Could not parse"));
        }

        tokens = rem_tokens;
        list.push(t);

        match tokens.first() {
            Some(t) if t == delimeter => tokens.skip_one(),
            Some(t) if !delimeter_terminated && t == end_token => break tokens.skip_one(),
            Some(t) if delimeter_terminated => bail!("expected {delimeter:?}, found {t:?}"),
            None if delimeter_terminated => bail!("expected {delimeter:?}, found end of tokens"),
            Some(t) => bail!("expected {delimeter:?} or {end_token:?}, found {t:?}"),
            None => bail!("expected {delimeter:?} or {end_token:?}, found end of tokens"),
        }
    }

    Ok((tokens, list))
}

impl<'a> Consume<'a> for Expr<'a> {
    fn consume(tokens: Parser<'a>) -> Result<(Parser<'a>, Expr<'a>)> {
        let (mut tokens, mut expr) = match tokens.first() {
            Some(Token::INTVAL(s)) => {
                tokens.skip_one();
                (tokens, Expr::Int(s.parse().wrap_err("parsing int expr")?))
            }
            Some(Token::FLOATVAL(s)) => {
                tokens.skip_one();
                (
                    tokens,
                    Expr::Float({
                        let f = s.parse::<f64>().wrap_err("parsing float expr")?;
                        if !f.is_finite() {
                            bail!("expected a finite float, found {f}");
                        } else {
                            f
                        }}

                    ),
                )
            }
            Some(Token::VOID) => {
                tokens.skip_one();
                (tokens, Expr::Void)
            }
            Some(Token::TRUE) => {
                tokens.skip_one();
                (tokens, Expr::True)
            }
            Some(Token::FALSE) => {
                tokens.skip_one();
                (tokens, Expr::False)
            }
            Some(Token::VARIABLE(s)) => {
                tokens.skip_one();
                (tokens, Expr::Variable(s))
            }
            Some(Token::LSQUARE) => {
                tokens.skip_one();

                let (tokens, exprs) = consume_list(tokens, Token::RSQUARE, Token::COMMA, false).wrap_err("parsing array literal expr")?;

                (tokens, Expr::Array(exprs))
            }
            Some(Token::LPAREN) => {
                tokens.skip_one();
                let (tokens, expr) = Expr::consume(tokens).wrap_err("parsing parenthesis expr")?;
                tokens.check_skip(Token::RPAREN).wrap_err("parsing parenthesis expr")?;
                (tokens, expr)
            }
            Some(Token::LCURLY) => {
                tokens.skip_one();
                let (tokens, exprs) = consume_list(tokens, Token::RCURLY, Token::COMMA, false).wrap_err("parsing tuple literal expr")?;
                (tokens, Expr::Tuple(exprs))
            }
            Some(t) => bail!(
                "expected start of expression (INTVAL | FLOATVAL | TRUE | FALSE | VARIABLE | LSQUARE | LPAREN | LCURLY), found {t:?}"
            ),
            None => bail!(
                "expected start of expression (INTVAL | FLOATVAL | TRUE | FALSE | VARIABLE | LSQUARE | LPAREN | LCURLY), found end of tokens"
            ),
        };

        let (tokens, expr) = loop {
            match (tokens.first(), &expr) {
                (Some(Token::LSQUARE), _) => {
                    tokens.skip_one();
                    let (rem_tokens, exprs) =
                        consume_list(tokens, Token::RSQUARE, Token::COMMA, false)
                            .wrap_err("parsing array index expr")?;
                    tokens = rem_tokens;
                    expr = Expr::ArrayIndex(Box::new(expr), exprs)
                }
                (Some(Token::LPAREN), Expr::Variable(s)) => {
                    let s = Variable(s);
                    tokens.skip_one();
                    let (rem_tokens, exprs) =
                        consume_list(tokens, Token::RPAREN, Token::COMMA, false)
                            .wrap_err("parsing call expr")?;
                    tokens = rem_tokens;
                    expr = Expr::Call(s, exprs)
                }
                (Some(Token::LCURLY), Expr::Variable(s)) => {
                    let s = Variable(s);
                    tokens.skip_one();
                    let (rem_tokens, exprs) =
                        consume_list(tokens, Token::RCURLY, Token::COMMA, false)
                            .wrap_err("parsing struct literal expr")?;
                    tokens = rem_tokens;
                    expr = Expr::StructLiteral(s, exprs)
                }
                (Some(Token::LCURLY), _) => {
                    tokens.skip_one();
                    let (rem_tokens, exprs) =
                        consume_list(tokens, Token::RCURLY, Token::COMMA, false)
                            .wrap_err("parsing tuple index expr")?;
                    tokens = rem_tokens;
                    expr = Expr::TupleIndex(Box::new(expr), exprs)
                }
                (Some(Token::DOT), _) => {
                    tokens.skip_one();
                    let (rem_tokens, var) =
                        Variable::consume(tokens).wrap_err("parsing dot expr")?;
                    tokens = rem_tokens;
                    expr = Expr::Dot(Box::new(expr), var)
                }
                _ => break (tokens, expr),
            };
        };

        // let (tokens, expr) = match tokens.first() {
        //     // // ? Only Eq right now to pass that bad test
        //     // Some(Token::OP(c @ Op::Eq)) => {
        //     //     tokens.skip_one();
        //     //     let (tokens, expr2) = Expr::consume(tokens).wrap_err("parsing binary op expr")?;
        //     //     (tokens, Expr::Binop(Box::new(expr), c, Box::new(expr2)))
        //     // }
        //     _ => (tokens, expr),
        // };

        Ok((tokens, expr))
    }

    fn get_name(&self) -> &'static str {
        "expression"
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum LValue<'a> {
    Var(Variable<'a>),
    Array(Variable<'a>, Vec<Variable<'a>>),
    Tuple(Vec<LValue<'a>>),
}

impl std::fmt::Display for LValue<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LValue::Var(s) => write!(f, "(VarLValue {s})"),
            LValue::Array(s, args) => {
                write!(
                    f,
                    "(ArrayLValue {s} {})",
                    args.print_joined(" ").map_err(|_| std::fmt::Error)?
                )
            }
            LValue::Tuple(lvs) => {
                write!(
                    f,
                    "(TupleLValue {})",
                    lvs.print_joined(" ").map_err(|_| std::fmt::Error)?
                )
            }
        }
    }
}

impl<'a> Consume<'a> for LValue<'a> {
    fn consume(tokens: Parser<'a>) -> Result<(Parser<'a>, Self)> {
        let (tokens, lv) = match tokens.first() {
            Some(Token::VARIABLE(s)) => {
                tokens.skip_one();
                (tokens, LValue::Var(Variable(s)))
            }
            Some(Token::LCURLY) => {
                tokens.skip_one();
                let (tokens, lvs) = consume_list(tokens, Token::RCURLY, Token::COMMA, false)
                    .wrap_err("parsing tuple lvalue")?;
                (tokens, LValue::Tuple(lvs))
            }
            Some(t) => bail!("expected start of lvalue (VARIABLE | LCURLY), found {t:?}"),
            None => bail!("expected start of lvalue (VARIABLE | LCURLY), found end of tokens"),
        };

        let (tokens, lv) = match (tokens.first(), &lv) {
            (Some(Token::LSQUARE), &LValue::Var(s)) => {
                tokens.skip_one();
                let (tokens, args) = consume_list(tokens, Token::RSQUARE, Token::COMMA, false)
                    .wrap_err("parsing array lvalue")?;
                (tokens, LValue::Array(s, args))
            }
            _ => (tokens, lv),
        };

        Ok((tokens, lv))
    }

    fn get_name(&self) -> &'static str {
        "lvalue"
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type<'a> {
    Struct(&'a str),
    Array(Box<Type<'a>>, u8),
    Float,
    Int,
    Bool,
    Void,
    Tuple(Vec<Type<'a>>),
}

impl std::fmt::Display for Type<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Struct(s) => write!(f, "(StructType {s})"),
            Type::Array(s, i) => write!(f, "(ArrayType {s} {i})"),
            Type::Float => write!(f, "(FloatType)"),
            Type::Int => write!(f, "(IntType)"),
            Type::Bool => write!(f, "(BoolType)"),
            Type::Void => write!(f, "(VoidType)"),
            Type::Tuple(tys) => {
                write!(
                    f,
                    "(TupleType {})",
                    tys.print_joined(" ").map_err(|_| std::fmt::Error)?
                )
            }
        }
    }
}

impl<'a> Consume<'a> for Type<'a> {
    fn consume(tokens: Parser<'a>) -> Result<(Parser<'a>, Self)> {
        let (tokens, mut ty) = match tokens.first() {
            Some(Token::VARIABLE(s)) => {
                tokens.skip_one();
                (tokens, Type::Struct(s))
            }
            Some(Token::INT) => {
                tokens.skip_one();
                (tokens, Type::Int)
            }
            Some(Token::BOOL) => {
                tokens.skip_one();
                (tokens, Type::Bool)
            }
            Some(Token::VOID) => {
                tokens.skip_one();
                (tokens, Type::Void)
            }
            Some(Token::FLOAT) => {
                tokens.skip_one();
                (tokens, Type::Float)
            }
            Some(Token::LCURLY) => {
                tokens.skip_one();
                let (tokens, tys) = consume_list(tokens, Token::RCURLY, Token::COMMA, false)
                    .wrap_err("parsing tuple type")?;
                (tokens, Type::Tuple(tys))
            }
            Some(t) => bail!("expected start of type (VARIABLE | FLOAT | LCURLY), found {t:?}"),
            None => {
                bail!("expected start of type (VARIABLE | FLOAT | LCURLY), found end of tokens")
            }
        };

        let (tokens, ty) = loop {
            match (tokens.first(), &ty) {
                (Some(Token::LSQUARE), _) => {
                    tokens.skip_one();

                    let mut depth: u8 = 1;

                    loop {
                        match tokens.next_and_skip().wrap_err("parsing array type")? {
                            Token::RSQUARE => {
                                break;
                            }
                            Token::COMMA => {
                                depth += 1;
                            }
                            t => bail!("expected RSQUARE or COMMA, found {t:?}"),
                        }
                    }

                    ty = Self::Array(Box::new(ty), depth);
                }
                _ => break (tokens, ty),
            };
        };

        Ok((tokens, ty))
    }

    fn get_name(&self) -> &'static str {
        "type"
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Binding<'a> {
    Var(LValue<'a>, Type<'a>),
}

impl std::fmt::Display for Binding<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Binding::Var(s, ty) => write!(f, "{s} {ty}"),
        }
    }
}

impl<'a> Consume<'a> for Binding<'a> {
    fn consume(tokens: Parser<'a>) -> Result<(Parser<'a>, Self)> {
        let (tokens, lv) = LValue::consume(tokens).wrap_err("parsing binding")?;
        tokens
            .check_skip(Token::COLON)
            .wrap_err("parsing binding")?;
        let (tokens, ty) = Type::consume(tokens).wrap_err("parsing binding")?;
        Ok((tokens, Self::Var(lv, ty)))
    }

    fn get_name(&self) -> &'static str {
        "binding"
    }
}

pub fn parse<'a>(
    tokens: &'a [Token<'a>],
    input_by_token: &'a [&'a str],
    source: &'a str,
) -> Result<Vec<Cmd<'a>>> {
    let mut cmds = vec![];

    let mut tokens = Parser {
        original_tokens: tokens,
        current_position: Cell::new(0),
        input_by_token,
        successfully_parsed: Rc::new(Cell::new(0)),
        source,
    };

    while !tokens.is_empty() {
        let cmd = Cmd::consume(tokens.clone());

        match cmd {
            Ok((moved_tokens, cmd)) => {
                debug_assert_ne!(moved_tokens, tokens);
                tokens = moved_tokens;
                tokens.successfully_parsed.set(0);
                cmds.push(cmd);
            }
            Err(e) => {
                if let Some(Token::NEWLINE) = tokens.first() {
                    tokens.skip_one();
                    continue;
                }

                if let Some(Token::END_OF_FILE) = tokens.first() {
                    break;
                }

                tokens.print_error();

                #[cfg(test)]
                println!("{e:?}");

                return Err(e);
            }
        }
    }

    Ok(cmds)
}

#[test]
fn test_parse_correct() {
    use regex::Regex;
    let regex = Regex::new(r"\n\s+").unwrap();

    let tester = |file: &str, solution_file: &str| {
        let (tokens, input_by_token) = crate::lex::lex(file).expect("Lexing should work");

        let parsed = match parse(&tokens, &input_by_token, file) {
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
    test_correct("grader/hw4/ok-fuzzer", tester);
}

#[test]
fn test_parse_fails() {
    let tester = |file: Option<&str>| {
        let Ok((tokens, input_by_tokens)) = crate::lex::lex(file.unwrap()) else {
            return;
        };

        match parse(&tokens, &input_by_tokens, file.unwrap()) {
            Ok(parsed) => {
                println!("{:?}", parsed);
                panic!("expected parse to fail");
            }
            Err(e) => {
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
}
