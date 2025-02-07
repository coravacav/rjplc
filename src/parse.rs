use std::{fmt::Write, path::Path};

use color_eyre::eyre::{bail, Result};
use colored::Colorize;
use itertools::Itertools;

use crate::{
    lex::{self, Token, TokenType},
    measure, undo_slice_by_cuts, CustomDisplay, UndoSliceSelection,
};

#[cfg(test)]
use crate::measure::print_timings;
#[cfg(test)]
use crate::{test_correct, test_solos};

trait Consume<'a, 'b>: Sized {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self>;
}

trait PrintJoined {
    fn print_joined(&self, f: &mut String, string_map: &[&str], sep: &str) -> std::fmt::Result;
}

impl<T: CustomDisplay> PrintJoined for [T] {
    fn print_joined(&self, f: &mut String, string_map: &[&str], sep: &str) -> std::fmt::Result {
        for (i, t) in self.iter().enumerate() {
            if i != 0 {
                f.write_str(sep)?;
            }
            t.fmt(f, string_map)?;
        }

        Ok(())
    }
}

enum ParseResult<'a, T> {
    NotParsedErrorPrinted {
        error_message: Box<dyn Fn() -> String + 'a>,
        line: usize,
        column: usize,
    },
    NotParsed {
        error_message: Box<dyn Fn() -> String + 'a>,
        position: usize,
    },
    Parsed(Parser, T),
}

macro_rules! miss {
    ($parser:ident, $($msg:tt)*) => {
        return $parser.miss(Box::new(move || format!($($msg)*)))
    };
}

macro_rules! consume {
    ($parser:ident, $data:ident, $type:ty, $outvar:ident) => {
        let (advanced_parser, $outvar) = match <$type>::consume($parser, $data) {
            ParseResult::Parsed(parser, t) => {
                debug_assert_ne!($parser.current_position, parser.current_position);
                (parser, t)
            }
            ParseResult::NotParsed {
                error_message,
                position,
            } => {
                return ParseResult::NotParsed {
                    error_message,
                    position,
                }
            }
            ParseResult::NotParsedErrorPrinted {
                error_message,
                line,
                column,
            } => {
                return ParseResult::NotParsedErrorPrinted {
                    error_message,
                    line,
                    column,
                }
            }
        };

        $parser = advanced_parser;
    };
}

fn consume_list<'a, 'b, T: Consume<'a, 'b> + std::fmt::Debug>(
    mut parser: Parser,
    data: &'b StaticParserData<'a>,
    end_token: TokenType,
    delimeter: TokenType,
    delimeter_terminated: bool,
) -> ParseResult<'a, Vec<T>> {
    let mut list = vec![];
    loop {
        if let ParseResult::Parsed(parser, ()) = parser.check_skip(data, end_token) {
            return parser.complete(list);
        }

        consume!(parser, data, T, t);
        list.push(t);

        match parser.first(data) {
            t if t.get_type() == delimeter => parser = parser.skip_one(),
            t if !delimeter_terminated && t.get_type() == end_token => {
                parser = parser.skip_one();
                return parser.complete(list);
            }
            t if delimeter_terminated => miss!(parser, "expected {delimeter:?}, found {t:?}"),
            t => miss!(
                parser,
                "expected {delimeter:?} or {end_token:?}, found {t:?}"
            ),
        }
    }
}

macro_rules! consume_list {
    ($parser:ident, $data:ident, $end_token:tt, $delimeter:tt, $delimeter_terminated:expr, $outvar:ident) => {
        let (advanced_parser, $outvar) = match consume_list(
            $parser,
            $data,
            TokenType::$end_token,
            TokenType::$delimeter,
            $delimeter_terminated,
        ) {
            ParseResult::Parsed(parser, t) => {
                debug_assert_ne!($parser.current_position, parser.current_position);
                (parser, t)
            }
            ParseResult::NotParsed {
                error_message,
                position,
            } => {
                return ParseResult::NotParsed {
                    error_message,
                    position,
                }
            }
            ParseResult::NotParsedErrorPrinted {
                error_message,
                line,
                column,
            } => {
                return ParseResult::NotParsedErrorPrinted {
                    error_message,
                    line,
                    column,
                }
            }
        };

        $parser = advanced_parser;
    };
    ($parser:ident, $data:ident, $end_token:tt, $delimeter:tt, $outvar:ident) => {
        consume_list!($parser, $data, $end_token, $delimeter, false, $outvar)
    };
    ($parser:ident, $data:ident, $end_token:tt, $outvar:ident) => {
        consume_list!($parser, $data, $end_token, COMMA, false, $outvar)
    };
}

macro_rules! check {
    ($parser:ident, $data:ident, $token:tt) => {
        let advanced_parser = match $parser.check_skip($data, TokenType::$token) {
            ParseResult::Parsed(parser, _) => (parser),
            ParseResult::NotParsed {
                error_message,
                position,
            } => {
                return ParseResult::NotParsed {
                    error_message,
                    position,
                }
            }
            ParseResult::NotParsedErrorPrinted {
                error_message,
                line,
                column,
            } => {
                return ParseResult::NotParsedErrorPrinted {
                    error_message,
                    line,
                    column,
                }
            }
        };

        $parser = advanced_parser;
    };
}

macro_rules! localize_error {
    ($parser:ident, $data:ident, $ty:ty, $function_body:expr) => {{
        fn inner_func<'a>(
            mut $parser: Parser,
            $data: &StaticParserData<'a>,
        ) -> ParseResult<'a, $ty> {
            $function_body
        }

        match inner_func($parser, $data) {
            ParseResult::NotParsed {
                error_message,
                position,
            } if position != $parser.current_position => {
                let (line, column) = $parser.print_error($data, position);
                ParseResult::NotParsedErrorPrinted {
                    error_message,
                    line,
                    column,
                }
            }
            t => t,
        }
    }};
}

#[derive(Clone, Copy, PartialEq)]
struct Parser {
    current_position: usize,
}

struct StaticParserData<'a> {
    original_tokens: &'a [Token],
    string_map: &'a [&'a str],
    source: &'a str,
}

impl<'a, 'b> Parser {
    fn complete<T>(self, t: T) -> ParseResult<'a, T> {
        ParseResult::Parsed(self, t)
    }

    fn miss<T>(self, report: Box<dyn Fn() -> String + 'a>) -> ParseResult<'a, T> {
        ParseResult::NotParsed {
            error_message: report,
            position: self.current_position,
        }
    }

    #[must_use]
    fn skip_one(mut self) -> Self {
        self.current_position += 1;
        self
    }

    fn check_skip(self, data: &'b StaticParserData<'a>, token: TokenType) -> ParseResult<'a, ()> {
        debug_assert_ne!(token, TokenType::END_OF_FILE);
        if self.check_one(data, token) {
            ParseResult::Parsed(self.skip_one(), ())
        } else {
            let first = self.first(data);
            ParseResult::NotParsed {
                error_message: Box::new(move || format!("expected {token:?}, found {first:?}")),
                position: self.current_position,
            }
        }
    }

    fn check_one(self, data: &StaticParserData<'a>, token: TokenType) -> bool {
        self.first(data).get_type() == token
    }

    fn first(self, data: &StaticParserData<'a>) -> Token {
        debug_assert!(data.original_tokens.get(self.current_position).is_some());
        // SAFETY: EOF is always at the end and we never check for EOF
        unsafe { *data.original_tokens.get_unchecked(self.current_position) }
    }

    fn first_type(self, data: &StaticParserData<'a>) -> TokenType {
        self.first(data).get_type()
    }

    fn next(self, data: &StaticParserData<'a>) -> (Self, Token) {
        let next = self.first(data);
        (self.skip_one(), next)
    }

    fn next_type(self, data: &StaticParserData<'a>) -> (Self, TokenType) {
        let next = self.first_type(data);
        (self.skip_one(), next)
    }

    fn is_empty(self, data: &StaticParserData<'a>) -> bool {
        self.current_position == data.original_tokens.len()
    }

    /// This function prints the error token text in red and the surrounding text.
    fn print_error(&self, data: &'b StaticParserData<'a>, error_position: usize) -> (usize, usize) {
        let current_position = self.current_position;

        let input_by_token = lex::input_by_token(data.source, data.original_tokens.len());

        let error_position = if error_position == input_by_token.len() {
            input_by_token.len() - 1
        } else {
            error_position
        };

        let [source_pre, semi_valid, error, source_post] = undo_slice_by_cuts(
            data.source,
            [
                UndoSliceSelection::Boundless,
                UndoSliceSelection::Beginning(input_by_token[current_position]),
                UndoSliceSelection::Beginning(input_by_token[error_position]),
                UndoSliceSelection::End(input_by_token[error_position]),
                UndoSliceSelection::Boundless,
            ],
        );

        let (source_pre, newlines) = {
            let mut src_iter = source_pre.split('\n').rev();

            let source_pre = src_iter
                .by_ref()
                .take(2)
                .map(|line| line.dimmed().to_string())
                .collect_vec()
                .iter()
                .rev()
                .join("\n");

            (source_pre, src_iter.count() + 1..)
        };

        // find the line and col of the error
        let (line, column) = {
            let mut line = 1;
            let mut column = 0;

            let start_ptr = data.source.as_ptr() as usize;
            let stop_ptr = input_by_token[error_position].as_ptr() as usize;

            for (i, c) in data.source.chars().enumerate() {
                if start_ptr + i == stop_ptr {
                    break;
                }

                if c == '\n' {
                    line += 1;
                    column = 0;
                } else {
                    column += 1;
                }
            }

            (line, column)
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

        let output = format!("{source_pre}{semi_valid}{error}{source_post}");
        let output = output
            .split('\n')
            .zip(newlines)
            .map(|(line, newline_count)| (newline_count, line))
            .collect_vec();

        let max_length_of_line_number = output
            .iter()
            .map(|(line_number, _)| line_number.to_string().len())
            .max()
            .unwrap();

        #[cfg(feature = "measure")]
        #[cfg(test)]
        return (line, column);

        for (line_number, line) in output {
            println!(
                "{}{line}",
                format!("{line_number:>max_length_of_line_number$} | ").bright_blue()
            );
        }
        println!();

        (line, column)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Variable(usize);

impl CustomDisplay for Variable {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        f.write_str(string_map[self.0])
    }
}

impl<'a, 'b> Consume<'a, 'b> for Variable {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("variable");
        let (parser, s) = match parser.next(data) {
            (parser, t) if t.get_type() == TokenType::VARIABLE => (parser, t.get_index()),
            (_, t) => miss!(parser, "expected variable, found {:?}", t),
        };

        parser.complete(Self(s))
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LiteralString(usize);

impl CustomDisplay for LiteralString {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        f.write_char('"')?;
        f.write_str(string_map[self.0])?;
        f.write_char('"')
    }
}

impl<'a, 'b> Consume<'a, 'b> for LiteralString {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("string_lit");
        let s = match parser.first(data) {
            t if t.get_type() == TokenType::STRING => t.get_index(),
            t => miss!(parser, "expected string, found {t:?}"),
        };

        parser.skip_one().complete(Self(s))
    }
}

#[derive(Debug, Clone)]
pub struct LoopField(Variable, Expr);

impl CustomDisplay for LoopField {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        self.0.fmt(f, string_map)?;
        f.write_char(' ')?;
        self.1.fmt(f, string_map)
    }
}

impl<'a, 'b> Consume<'a, 'b> for LoopField {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("arraySumField");
        localize_error!(parser, data, LoopField, {
            consume!(parser, data, Variable, s);
            check!(parser, data, COLON);
            consume!(parser, data, Expr, expr);
            parser.complete(LoopField(s, expr))
        })
    }
}

#[derive(Debug, Clone)]
pub struct Field(Variable, Type);

impl CustomDisplay for Field {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        self.0.fmt(f, string_map)?;
        f.write_char(' ')?;
        self.1.fmt(f, string_map)
    }
}

impl<'a, 'b> Consume<'a, 'b> for Field {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("field");
        localize_error!(parser, data, Field, {
            consume!(parser, data, Variable, s);
            check!(parser, data, COLON);
            consume!(parser, data, Type, ty);
            parser.complete(Field(s, ty))
        })
    }
}

#[derive(Debug, Clone)]
pub enum Cmd {
    Read(LiteralString, LValue),
    Write(Expr, LiteralString),
    Let(LValue, Expr),
    Assert(Expr, LiteralString),
    Print(LiteralString),
    Show(Expr),
    Time(Box<Cmd>),
    Fn(Variable, Vec<Binding>, Type, Vec<Statement>),
    Type(Variable, Type),
    Struct(Variable, Vec<Field>),
}

impl<'a, 'b> Consume<'a, 'b> for Cmd {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("cmd");
        match parser.next_type(data) {
            (mut parser, TokenType::READ) => {
                check!(parser, data, IMAGE);
                consume!(parser, data, LiteralString, s);
                check!(parser, data, TO);
                consume!(parser, data, LValue, lvalue);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Read(s, lvalue))
            }
            (mut parser, TokenType::TIME) => {
                consume!(parser, data, Cmd, cmd);
                parser.complete(Self::Time(Box::new(cmd)))
            }
            (mut parser, TokenType::LET) => {
                consume!(parser, data, LValue, lvalue);
                check!(parser, data, EQUALS);
                consume!(parser, data, Expr, expr);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Let(lvalue, expr))
            }
            (mut parser, TokenType::ASSERT) => {
                consume!(parser, data, Expr, expr);
                check!(parser, data, COMMA);
                consume!(parser, data, LiteralString, s);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Assert(expr, s))
            }
            (mut parser, TokenType::SHOW) => {
                consume!(parser, data, Expr, expr);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Show(expr))
            }
            (mut parser, TokenType::WRITE) => {
                check!(parser, data, IMAGE);
                consume!(parser, data, Expr, expr);
                check!(parser, data, TO);
                consume!(parser, data, LiteralString, s);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Write(expr, s))
            }
            (mut parser, TokenType::PRINT) => {
                consume!(parser, data, LiteralString, s);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Print(s))
            }
            (mut parser, TokenType::FN) => {
                consume!(parser, data, Variable, v);
                check!(parser, data, LPAREN);
                consume_list!(parser, data, RPAREN, bindings);
                check!(parser, data, COLON);
                consume!(parser, data, Type, ty);
                check!(parser, data, LCURLY);
                check!(parser, data, NEWLINE);
                consume_list!(parser, data, RCURLY, NEWLINE, true, statements);
                parser.complete(Self::Fn(v, bindings, ty, statements))
            }
            (mut parser, TokenType::TYPE) => {
                consume!(parser, data, Variable, v);
                check!(parser, data, EQUALS);
                consume!(parser, data, Type, ty);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Type(v, ty))
            }
            (mut parser, TokenType::STRUCT) => {
                consume!(parser, data, Variable, v);
                check!(parser, data, LCURLY);
                check!(parser, data, NEWLINE);
                consume_list!(parser, data, RCURLY, NEWLINE, fields);
                parser.complete(Self::Struct(v, fields))
            }
            (_, t) => miss!(parser, "expected a command keyword (ASSERT | RETURN | LET | ASSERT | PRINT | SHOW | TIME | FN | TYPE | STRUCT), found {t:?}"),
        }
    }
}

impl CustomDisplay for Cmd {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match self {
            Cmd::Read(file, lvalue) => {
                f.write_str("(ReadCmd ")?;
                file.fmt(f, string_map)?;
                f.write_char(' ')?;
                lvalue.fmt(f, string_map)?;
                f.write_char(')')
            }
            Cmd::Write(expr, file) => {
                f.write_str("(WriteCmd ")?;
                expr.fmt(f, string_map)?;
                f.write_char(' ')?;
                file.fmt(f, string_map)?;
                f.write_char(')')
            }
            Cmd::Let(lvalue, expr) => {
                f.write_str("(LetCmd ")?;
                lvalue.fmt(f, string_map)?;
                f.write_char(' ')?;
                expr.fmt(f, string_map)?;
                f.write_char(')')
            }
            Cmd::Assert(expr, msg) => {
                f.write_str("(AssertCmd ")?;
                expr.fmt(f, string_map)?;
                f.write_char(' ')?;
                msg.fmt(f, string_map)?;
                f.write_char(')')
            }
            Cmd::Print(msg) => {
                f.write_str("(PrintCmd ")?;
                msg.fmt(f, string_map)?;
                f.write_char(')')
            }
            Cmd::Show(expr) => {
                f.write_str("(ShowCmd ")?;
                expr.fmt(f, string_map)?;
                f.write_char(')')
            }
            Cmd::Time(cmd) => {
                f.write_str("(TimeCmd ")?;
                cmd.fmt(f, string_map)?;
                f.write_char(')')
            }
            Cmd::Fn(name, bindings, ty, statements) => {
                f.write_str("(FnCmd ")?;
                name.fmt(f, string_map)?;
                f.write_str(" ((")?;
                bindings.print_joined(f, string_map, " ")?;
                f.write_str(")) ")?;
                ty.fmt(f, string_map)?;
                f.write_char(' ')?;
                statements.print_joined(f, string_map, " ")?;
                f.write_char(')')
            }
            Cmd::Type(name, ty) => {
                f.write_str("(TypeCmd ")?;
                name.fmt(f, string_map)?;
                f.write_char(' ')?;
                ty.fmt(f, string_map)?;
                f.write_char(')')
            }
            Cmd::Struct(name, fields) => {
                f.write_str("(StructCmd ")?;
                name.fmt(f, string_map)?;
                if !fields.is_empty() {
                    f.write_char(' ')?;
                    fields.print_joined(f, string_map, " ")?;
                }
                f.write_char(')')
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Statement {
    Let(LValue, Expr),
    Assert(Expr, LiteralString),
    Return(Expr),
}

impl CustomDisplay for Statement {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match self {
            Statement::Let(lvalue, expr) => {
                f.write_str("(LetStmt ")?;
                lvalue.fmt(f, string_map)?;
                f.write_char(' ')?;
                expr.fmt(f, string_map)?;
                f.write_char(')')
            }
            Statement::Assert(expr, msg) => {
                f.write_str("(AssertStmt ")?;
                expr.fmt(f, string_map)?;
                f.write_char(' ')?;
                msg.fmt(f, string_map)?;
                f.write_char(')')
            }
            Statement::Return(expr) => {
                f.write_str("(ReturnStmt ")?;
                expr.fmt(f, string_map)?;
                f.write_char(')')
            }
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Statement {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("statement");
        localize_error!(parser, data, Statement, {
            match parser.first_type(data) {
                TokenType::ASSERT => {
                    parser = parser.skip_one();
                    consume!(parser, data, Expr, expr);
                    check!(parser, data, COMMA);
                    consume!(parser, data, LiteralString, msg);
                    parser.complete(Statement::Assert(expr, msg))
                }
                TokenType::RETURN => {
                    parser = parser.skip_one();
                    consume!(parser, data, Expr, expr);
                    parser.complete(Statement::Return(expr))
                }
                TokenType::LET => {
                    parser = parser.skip_one();
                    consume!(parser, data, LValue, lvalue);
                    check!(parser, data, EQUALS);
                    consume!(parser, data, Expr, expr);
                    parser.complete(Statement::Let(lvalue, expr))
                }
                t => miss!(
                    parser,
                    "expected a start of statement (ASSERT | RETURN | LET), found {t:?}"
                ),
            }
        })
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub struct Op(TokenType);

impl Op {
    const fn precedence(self) -> u8 {
        match self.0 {
            TokenType::Add | TokenType::Sub => 4,
            TokenType::Mul | TokenType::Div | TokenType::Mod => 5,
            TokenType::Less
            | TokenType::Greater
            | TokenType::LessEq
            | TokenType::GreaterEq
            | TokenType::Eq
            | TokenType::Neq => 3,
            TokenType::And | TokenType::Or => 2,
            TokenType::Not => u8::MAX,
            _ => unreachable!(),
        }
    }
}

impl From<TokenType> for Op {
    fn from(token: TokenType) -> Self {
        Op(token)
    }
}

impl CustomDisplay for Op {
    fn fmt(&self, f: &mut String, _string_map: &[&str]) -> std::fmt::Result {
        match self.0 {
            TokenType::Add => f.write_str("+"),
            TokenType::Sub => f.write_str("-"),
            TokenType::Mul => f.write_str("*"),
            TokenType::Div => f.write_str("/"),
            TokenType::Mod => f.write_str("%"),
            TokenType::Not => f.write_str("!"),
            TokenType::Greater => f.write_str(">"),
            TokenType::Less => f.write_str("<"),
            TokenType::Eq => f.write_str("=="),
            TokenType::Neq => f.write_str("!="),
            TokenType::And => f.write_str("&&"),
            TokenType::Or => f.write_str("||"),
            TokenType::GreaterEq => f.write_str(">="),
            TokenType::LessEq => f.write_str("<="),
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Int(i64, usize),
    Float(f64, usize),
    True,
    False,
    Void,
    Variable(Variable),
    ArrayLiteral(Vec<Expr>),
    TupleLiteral(Vec<Expr>),
    Paren(Box<Expr>),
    ArrayIndex(Box<Expr>, Vec<Expr>),
    Binop(Box<Expr>, Op, Box<Expr>),
    Call(Variable, Vec<Expr>),
    TupleIndex(Box<Expr>, Vec<Expr>),
    StructLiteral(Variable, Vec<Expr>),
    Dot(Box<Expr>, Variable),
    Unop(Op, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    ArrayLoop(Vec<LoopField>, Box<Expr>),
    SumLoop(Vec<LoopField>, Box<Expr>),
}

impl Expr {
    const UNOP_PRECEDENCE: u8 = 6;

    const fn precedence(&self) -> u8 {
        match self {
            Expr::TupleIndex(_, _) | Expr::ArrayIndex(_, _) => 7,
            Expr::Unop(_, _) => Self::UNOP_PRECEDENCE,
            Expr::Binop(_, op, _) => op.precedence(),
            Expr::If(_, _, _) | Expr::ArrayLoop(_, _) | Expr::SumLoop(_, _) => 1,
            _ => u8::MAX,
        }
    }
}

impl CustomDisplay for Expr {
    #[allow(clippy::too_many_lines)]
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match self {
            Expr::Int(_, i) => write!(f, "(IntExpr {})", {
                let i = string_map[*i].trim_start_matches('0');
                if i.is_empty() {
                    "0"
                } else {
                    i
                }
            }),
            Expr::Float(fl, s_fl) => string_map[*s_fl]
                .split_once('.')
                .map(|(trunc, _)| {
                    let trunc = trunc.trim_start_matches('0');
                    if trunc.is_empty() {
                        write!(f, "(FloatExpr 0)")
                    } else if trunc.len() > 15 {
                        write!(f, "(FloatExpr {})", fl.trunc())
                    } else {
                        write!(f, "(FloatExpr {trunc})")
                    }
                })
                .unwrap(),
            Expr::True => write!(f, "(TrueExpr)"),
            Expr::False => write!(f, "(FalseExpr)"),
            Expr::Void => write!(f, "(VoidExpr)"),
            Expr::Variable(s) => {
                f.write_str("(VarExpr ")?;
                s.fmt(f, string_map)?;
                f.write_char(')')
            }
            Expr::Paren(expr) => expr.fmt(f, string_map),
            Expr::ArrayLiteral(exprs) => {
                if exprs.is_empty() {
                    f.write_str("(ArrayLiteralExpr)")
                } else {
                    f.write_str("(ArrayLiteralExpr ")?;
                    exprs.print_joined(f, string_map, " ")?;
                    f.write_char(')')
                }
            }
            Expr::TupleLiteral(exprs) => {
                f.write_str("(TupleLiteralExpr ")?;
                exprs.print_joined(f, string_map, " ")?;
                f.write_char(')')
            }
            Expr::ArrayIndex(s, exprs) => {
                f.write_str("(ArrayIndexExpr ")?;
                s.fmt(f, string_map)?;
                if !exprs.is_empty() {
                    f.write_char(' ')?;
                    exprs.print_joined(f, string_map, " ")?;
                }
                write!(f, ")")
            }
            Expr::TupleIndex(s, exprs) => {
                f.write_str("(TupleIndexExpr ")?;
                s.fmt(f, string_map)?;
                f.write_char(' ')?;
                exprs.print_joined(f, string_map, " ")?;
                f.write_char(')')
            }
            Expr::Binop(expr, op, expr2) => {
                f.write_str("(BinopExpr ")?;
                expr.fmt(f, string_map)?;
                f.write_char(' ')?;
                op.fmt(f, string_map)?;
                f.write_char(' ')?;
                expr2.fmt(f, string_map)?;
                f.write_char(')')
            }
            Expr::Call(expr, exprs) => {
                f.write_str("(CallExpr ")?;
                expr.fmt(f, string_map)?;
                if !exprs.is_empty() {
                    f.write_char(' ')?;
                    exprs.print_joined(f, string_map, " ")?;
                }
                write!(f, ")")
            }
            Expr::StructLiteral(s, exprs) => {
                f.write_str("(StructLiteralExpr ")?;
                s.fmt(f, string_map)?;
                if !exprs.is_empty() {
                    f.write_char(' ')?;
                    exprs.print_joined(f, string_map, " ")?;
                }
                write!(f, ")")
            }
            Expr::Dot(expr, s) => {
                f.write_str("(DotExpr ")?;
                expr.fmt(f, string_map)?;
                f.write_char(' ')?;
                s.fmt(f, string_map)?;
                write!(f, ")")
            }
            Expr::Unop(op, expr) => {
                f.write_str("(UnopExpr ")?;
                op.fmt(f, string_map)?;
                f.write_char(' ')?;
                expr.fmt(f, string_map)?;
                write!(f, ")")
            }
            Expr::If(expr, expr2, expr3) => {
                f.write_str("(IfExpr ")?;
                expr.fmt(f, string_map)?;
                f.write_char(' ')?;
                expr2.fmt(f, string_map)?;
                f.write_char(' ')?;
                expr3.fmt(f, string_map)?;
                write!(f, ")")
            }
            Expr::ArrayLoop(fields, expr) => {
                f.write_str("(ArrayLoopExpr ")?;
                if !fields.is_empty() {
                    fields.print_joined(f, string_map, " ")?;
                    f.write_char(' ')?;
                }
                expr.fmt(f, string_map)?;
                write!(f, ")")
            }
            Expr::SumLoop(fields, expr) => {
                f.write_str("(SumLoopExpr ")?;
                if !fields.is_empty() {
                    fields.print_joined(f, string_map, " ")?;
                    f.write_char(' ')?;
                }
                expr.fmt(f, string_map)?;
                write!(f, ")")
            }
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Expr {
    #[allow(clippy::too_many_lines)]
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("expr");
        let next = parser.next(data);
        let (mut parser, mut expr) = match (next.0, next.1.get_type()) {
            (mut parser, op @ (TokenType::Not | TokenType::Sub)) => {
                measure!("unop");
                fn rearrange_according_to_precedence(
                    op: Op,
                    right_expr: Expr,
                ) -> Expr {
                    if Expr::UNOP_PRECEDENCE < right_expr.precedence() {
                        Expr::Unop(op, Box::new(right_expr))
                    } else {
                        match right_expr {
                            Expr::Binop(mut right_expr_left, c2, right_expr_right) => Expr::Binop(
                                {
                                    // reuxe the allocation from right_expr_left 
                                    *right_expr_left = rearrange_according_to_precedence(op,*right_expr_left);
                                    right_expr_left
                                },
                                c2,
                                right_expr_right,
                            ),
                            expr => Expr::Unop(op, Box::new(expr)),
                        }
                    }
                }

                consume!(parser, data, Expr, expr);
                (parser, rearrange_according_to_precedence(op.into(), expr))
            }
            (parser, TokenType::INTVAL) => {
                let si = next.1.get_index();
                let s = data.string_map[si];
                if let Ok(i) = s.parse::<i64>() {
                    (parser, Expr::Int(i, si))
                } else {
                    miss!(parser, "couldn't parse integer {s}")
                }
            }
            (parser, TokenType::FLOATVAL) => {
                let si = next.1.get_index();
                let s = data.string_map[si];
                if let Ok(f) = s.parse::<f64>() {
                    if !f.is_finite() {
                        miss!(parser, "expected a finite float, found {f}");
                    }

                    (parser, Expr::Float(f, si))
                } else {
                    miss!(parser, "couldn't parse float {s}")
                }
            }
            (parser, TokenType::VOID) => (parser, Expr::Void),
            (parser, TokenType::TRUE) => (parser, Expr::True),
            (parser, TokenType::FALSE) => (parser, Expr::False),
            (parser, TokenType::VARIABLE) => (parser, Expr::Variable(Variable(next.1.get_index()))),
            (mut parser, TokenType::LSQUARE) => {
                consume_list!(parser, data, RSQUARE, exprs);
                (parser, Expr::ArrayLiteral(exprs))
            }
            (mut parser, TokenType::LPAREN) => {
                consume!(parser, data, Expr, expr);
                check!(parser, data, RPAREN);
                (parser, Expr::Paren(Box::new(expr)))
            }
            (mut parser, TokenType::LCURLY) => {
                consume_list!(parser, data, RCURLY, exprs);
                (parser, Expr::TupleLiteral(exprs))
            }
            (mut parser, TokenType::IF) => {
                consume!(parser, data, Expr, expr);
                check!(parser, data, THEN);
                consume!(parser, data, Expr, expr2);
                check!(parser, data, ELSE);
                consume!(parser, data, Expr, expr3);
                (parser, Expr::If(Box::new(expr), Box::new(expr2), Box::new(expr3)))
            }
            (mut parser, TokenType::ARRAY) => {
                check!(parser, data, LSQUARE);
                consume_list!(parser, data, RSQUARE, fields);
                consume!(parser, data, Expr, expr);
                (parser, Expr::ArrayLoop(fields, Box::new(expr)))
            }
            (mut parser, TokenType::SUM) => {
                check!(parser, data, LSQUARE);
                consume_list!(parser, data, RSQUARE, fields);
                consume!(parser, data, Expr, expr);
                (parser, Expr::SumLoop(fields, Box::new(expr)))
            }
            (_, t) => miss!(parser,
                "expected start of expression (INTVAL | FLOATVAL | TRUE | FALSE | VARIABLE | LSQUARE | LPAREN | LCURLY), found {t:?}"
            ),
        };

        let (parser, expr) = loop {
            let (rem_parser, new_expr) = match (parser.next_type(data), &expr) {
                ((mut parser, TokenType::LSQUARE), _) => {
                    consume_list!(parser, data, RSQUARE, exprs);
                    (parser, Expr::ArrayIndex(Box::new(expr), exprs))
                }
                ((mut parser, TokenType::LPAREN), Expr::Variable(s)) => {
                    consume_list!(parser, data, RPAREN, exprs);
                    (parser, Expr::Call(*s, exprs))
                }
                ((mut parser, TokenType::LCURLY), Expr::Variable(s)) => {
                    consume_list!(parser, data, RCURLY, exprs);
                    (parser, Expr::StructLiteral(*s, exprs))
                }
                ((mut parser, TokenType::LCURLY), _) => {
                    consume_list!(parser, data, RCURLY, exprs);
                    (parser, Expr::TupleIndex(Box::new(expr), exprs))
                }
                ((mut parser, TokenType::DOT), _) => {
                    consume!(parser, data, Variable, var);
                    (parser, Expr::Dot(Box::new(expr), var))
                }
                (
                    (
                        mut parser,
                        op @ (TokenType::Add
                        | TokenType::Sub
                        | TokenType::Mul
                        | TokenType::Div
                        | TokenType::Mod
                        | TokenType::Greater
                        | TokenType::Less
                        | TokenType::Eq
                        | TokenType::Neq
                        | TokenType::And
                        | TokenType::Or
                        | TokenType::GreaterEq
                        | TokenType::LessEq),
                    ),
                    _,
                ) => {
                    measure!("binop");
                    fn rearrange_according_to_precedence(
                        new_expr: Expr,
                        op: Op,
                        right_expr: Expr,
                    ) -> Expr {
                        if op.precedence() < right_expr.precedence() {
                            Expr::Binop(Box::new(new_expr), op, Box::new(right_expr))
                        } else {
                            match right_expr {
                                Expr::Binop(mut right_expr_left, c2, right_expr_right) => {
                                    Expr::Binop(
                                        {
                                            // reuxe the allocation from right_expr_left
                                            *right_expr_left = rearrange_according_to_precedence(
                                                new_expr,
                                                op,
                                                *right_expr_left,
                                            );
                                            right_expr_left
                                        },
                                        c2,
                                        right_expr_right,
                                    )
                                }
                                _ => Expr::Binop(Box::new(new_expr), op, Box::new(right_expr)),
                            }
                        }
                    }

                    consume!(parser, data, Expr, expr2);
                    (
                        parser,
                        rearrange_according_to_precedence(expr, op.into(), expr2),
                    )
                }
                _ => break (parser, expr),
            };
            parser = rem_parser;
            expr = new_expr;
        };

        parser.complete(expr)
    }
}

#[derive(Debug, Clone)]
pub enum LValue {
    Var(Variable),
    Array(Variable, Vec<Variable>),
    Tuple(Vec<LValue>),
}

impl CustomDisplay for LValue {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match self {
            LValue::Var(s) => {
                f.write_str("(VarLValue ")?;
                s.fmt(f, string_map)?;
                write!(f, ")")
            }
            LValue::Array(s, args) => {
                f.write_str("(ArrayLValue ")?;
                s.fmt(f, string_map)?;
                f.write_char(' ')?;
                args.print_joined(f, string_map, " ")?;
                write!(f, ")")
            }
            LValue::Tuple(lvs) => {
                f.write_str("(TupleLValue ")?;
                lvs.print_joined(f, string_map, " ")?;
                write!(f, ")")
            }
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for LValue {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("lvalue");
        let next = parser.next(data);
        let (parser, lv) = match (next.0, next.1.get_type()) {
            (parser, TokenType::VARIABLE) => (parser, LValue::Var(Variable(next.1.get_index()))),
            (mut parser, TokenType::LCURLY) => {
                consume_list!(parser, data, RCURLY, lvs);
                (parser, LValue::Tuple(lvs))
            }
            (_, t) => miss!(
                parser,
                "expected start of lvalue (VARIABLE | LCURLY), found {t:?}"
            ),
        };

        let (parser, lv) = match (parser.next_type(data), &lv) {
            ((mut parser, TokenType::LSQUARE), &LValue::Var(s)) => {
                consume_list!(parser, data, RSQUARE, args);
                (parser, LValue::Array(s, args))
            }
            _ => (parser, lv),
        };

        parser.complete(lv)
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    // TODO maybe add wrapping type?
    Struct(usize),
    Array(Box<Type>, u8),
    Float,
    Int,
    Bool,
    Void,
    Tuple(Vec<Type>),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Struct(s), Type::Struct(o)) => s == o,
            (Type::Array(s, _), Type::Array(o, _)) => std::ptr::eq(&**s, &**o),
            (Type::Float, Type::Float)
            | (Type::Int, Type::Int)
            | (Type::Bool, Type::Bool)
            | (Type::Void, Type::Void) => true,
            (Type::Tuple(s), Type::Tuple(o)) => s.as_ptr() == o.as_ptr(),
            _ => false,
        }
    }
}

impl CustomDisplay for Type {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match self {
            Type::Struct(s) => {
                f.write_str("(StructType ")?;
                f.write_str(string_map[*s])?;
                // s.fmt(f, string_map)?; Based on TODO above.
                f.write_char(')')
            }
            Type::Array(s, i) => {
                f.write_str("(ArrayType ")?;
                s.fmt(f, string_map)?;
                f.write_char(' ')?;
                write!(f, "{i}")?;
                f.write_char(')')
            }
            Type::Float => f.write_str("(FloatType)"),
            Type::Int => f.write_str("(IntType)"),
            Type::Bool => f.write_str("(BoolType)"),
            Type::Void => f.write_str("(VoidType)"),
            Type::Tuple(tys) => {
                f.write_str("(TupleType ")?;
                tys.print_joined(f, string_map, " ")?;
                f.write_char(')')
            }
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Type {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("type");
        let next = parser.next(data);
        let (mut parser, mut ty) = match (next.0, next.1.get_type()) {
            (parser, TokenType::VARIABLE) => (parser, Type::Struct(next.1.get_index())),
            (parser, TokenType::INT) => (parser, Type::Int),
            (parser, TokenType::BOOL) => (parser, Type::Bool),
            (parser, TokenType::VOID) => (parser, Type::Void),
            (parser, TokenType::FLOAT) => (parser, Type::Float),
            (mut parser, TokenType::LCURLY) => {
                consume_list!(parser, data, RCURLY, tys);
                (parser, Type::Tuple(tys))
            }
            (_, t) => miss!(
                parser,
                "expected start of type (VARIABLE | FLOAT | LCURLY), found {t:?}"
            ),
        };

        #[allow(clippy::while_let_loop)]
        loop {
            match (parser.first_type(data), &ty) {
                (TokenType::LSQUARE, _) => {
                    parser = parser.skip_one();

                    let mut depth: u8 = 1;

                    loop {
                        match parser.next_type(data) {
                            (advanced_parser, TokenType::RSQUARE) => {
                                parser = advanced_parser;
                                break;
                            }
                            (advanced_parser, TokenType::COMMA) => {
                                parser = advanced_parser;
                                depth += 1;
                            }
                            (_, t) => miss!(parser, "expected RSQUARE or COMMA, found {t:?}"),
                        }
                    }

                    ty = Self::Array(Box::new(ty), depth);
                }
                _ => break,
            };
        }

        parser.complete(ty)
    }
}

#[derive(Debug, Clone)]
pub enum Binding {
    Var(LValue, Type),
}

impl CustomDisplay for Binding {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match self {
            Binding::Var(s, ty) => {
                s.fmt(f, string_map)?;
                f.write_char(' ')?;
                ty.fmt(f, string_map)
            }
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Binding {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("binding");
        localize_error!(parser, data, Binding, {
            consume!(parser, data, LValue, lv);
            check!(parser, data, COLON);
            consume!(parser, data, Type, ty);
            parser.complete(Binding::Var(lv, ty))
        })
    }
}

/// Parse the input string
///
/// # Errors
/// Something
pub fn parse<'a>(
    tokens: &'a [Token],
    string_map: &'a [&'a str],
    source: &'a str,
    path: &'a Path,
) -> Result<Vec<Cmd>> {
    measure!("parse");
    let mut cmds = vec![];

    let mut parser = Parser {
        current_position: 0,
    };

    let data = StaticParserData {
        original_tokens: tokens,
        string_map,
        source,
    };

    let data = &data;

    while !parser.is_empty(data) {
        let cmd = Cmd::consume(parser, data);

        match cmd {
            ParseResult::Parsed(moved_parser, cmd) => {
                // debug_assert_ne!(moved_parser, parser);
                parser = moved_parser;

                let cmd: Cmd = cmd;

                cmds.push(cmd);
            }
            pr => {
                if let TokenType::NEWLINE = parser.first_type(data) {
                    parser = parser.skip_one();
                    continue;
                }

                if let TokenType::END_OF_FILE = parser.first_type(data) {
                    break;
                }

                let (e, line, column) = match pr {
                    ParseResult::NotParsed {
                        error_message: e,
                        position: err_position,
                    } => {
                        let (line, column) = parser.print_error(data, err_position);
                        (e, line, column)
                    }
                    ParseResult::NotParsedErrorPrinted {
                        error_message: e,
                        line,
                        column,
                    } => (e, line, column),
                    ParseResult::Parsed(..) => unreachable!(),
                };

                bail!(
                    "{}",
                    format!("{} at {}:{}:{}", e(), path.display(), line, column)
                );
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
        let (tokens, string_map) = crate::lex::lex(file).expect("Lexing should work");

        let parsed = match parse(&tokens, &string_map, file, Path::new("")) {
            Ok(parsed) => parsed,
            Err(e) => {
                panic!("Compilation failed {e}");
            }
        };

        let mut output = String::new();

        for parsed in parsed {
            parsed.fmt(&mut output, &string_map).unwrap();
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
