use std::path::Path;

use color_eyre::eyre::{bail, Result};
use colored::Colorize;
use itertools::Itertools;

use crate::{
    lex::{Op, Token},
    measure, undo_slice_by_cuts, UndoSliceSelection,
};

#[cfg(test)]
use crate::lex::LexImplementation;
#[cfg(test)]
use crate::measure::print_timings;
#[cfg(test)]
use crate::{test_correct, test_solos};

trait Consume<'a, 'b>: Sized {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self>;
}

trait PrintJoined {
    fn print_joined(&self, f: &mut std::fmt::Formatter<'_>, sep: &str) -> std::fmt::Result;
}

impl<T: std::fmt::Display + std::fmt::Debug> PrintJoined for [T] {
    fn print_joined(&self, f: &mut std::fmt::Formatter<'_>, sep: &str) -> std::fmt::Result {
        for (i, t) in self.iter().enumerate() {
            if i != 0 {
                write!(f, "{sep}")?;
            }
            write!(f, "{t}")?;
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
    end_token: Token<'a>,
    delimeter: Token<'a>,
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
            t if t == delimeter => parser = parser.skip_one(),
            t if !delimeter_terminated && t == end_token => {
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
            Token::$end_token,
            Token::$delimeter,
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
        let advanced_parser = match $parser.check_skip($data, Token::$token) {
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
        fn inner_func<'a, 'b>(
            mut $parser: Parser,
            $data: &'b StaticParserData<'a>,
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
    original_tokens: &'a [Token<'a>],
    input_by_token: &'a [&'a str],
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

    fn check_skip(self, data: &'b StaticParserData<'a>, token: Token<'a>) -> ParseResult<'a, ()> {
        debug_assert_ne!(token, Token::END_OF_FILE);
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

    fn check_one(self, data: &StaticParserData<'a>, token: Token<'a>) -> bool {
        self.first(data) == token
    }

    fn first(self, data: &StaticParserData<'a>) -> Token<'a> {
        debug_assert!(data.original_tokens.get(self.current_position).is_some());
        // SAFETY: EOF is always at the end and we never check for EOF
        unsafe { *data.original_tokens.get_unchecked(self.current_position) }
    }

    fn next(self, data: &StaticParserData<'a>) -> (Self, Token<'a>) {
        let next = self.first(data);
        (self.skip_one(), next)
    }

    fn is_empty(self, data: &StaticParserData<'a>) -> bool {
        self.current_position == data.original_tokens.len()
    }

    /// This function prints the error token text in red and the surrounding text.
    fn print_error(&self, data: &'b StaticParserData<'a>, error_position: usize) -> (usize, usize) {
        let current_position = self.current_position;

        let error_position = if error_position == data.input_by_token.len() {
            data.input_by_token.len() - 1
        } else {
            error_position
        };

        let [source_pre, semi_valid, error, source_post] = undo_slice_by_cuts(
            data.source,
            [
                UndoSliceSelection::Boundless,
                UndoSliceSelection::Beginning(data.input_by_token[current_position]),
                UndoSliceSelection::Beginning(data.input_by_token[error_position]),
                UndoSliceSelection::End(data.input_by_token[error_position]),
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
            let stop_ptr = data.input_by_token[error_position].as_ptr() as usize;

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
pub struct Variable<'a>(&'a str);

impl std::fmt::Display for Variable<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}

impl<'a, 'b> Consume<'a, 'b> for Variable<'a> {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("variable");
        let (parser, s) = match parser.next(data) {
            (parser, Token::VARIABLE(s)) => (parser, s),
            (_, t) => miss!(parser, "expected variable, found {}", t),
        };

        parser.complete(Self(s))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LiteralString<'a>(&'a str);

impl PartialEq for LiteralString<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ptr() == other.0.as_ptr()
    }
}

impl std::fmt::Display for LiteralString<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
}

impl<'a, 'b> Consume<'a, 'b> for LiteralString<'a> {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("string_lit");
        let s = match parser.first(data) {
            Token::STRING(s) => s,
            t => miss!(parser, "expected string, found {t:?}"),
        };

        parser.skip_one().complete(Self(s))
    }
}

#[derive(Debug, Clone)]
pub struct LoopField<'a>(Variable<'a>, Expr<'a>);

impl std::fmt::Display for LoopField<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.0, self.1)
    }
}

impl<'a, 'b> Consume<'a, 'b> for LoopField<'a> {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("arraySumField");
        localize_error!(parser, data, LoopField<'a>, {
            consume!(parser, data, Variable, s);
            check!(parser, data, COLON);
            consume!(parser, data, Expr, expr);
            parser.complete(LoopField(s, expr))
        })
    }
}

#[derive(Debug, Clone)]
pub struct Field<'a>(Variable<'a>, Type<'a>);

impl std::fmt::Display for Field<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.0, self.1)
    }
}

impl<'a, 'b> Consume<'a, 'b> for Field<'a> {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("field");
        localize_error!(parser, data, Field<'a>, {
            consume!(parser, data, Variable, s);
            check!(parser, data, COLON);
            consume!(parser, data, Type, ty);
            parser.complete(Field(s, ty))
        })
    }
}

#[derive(Debug, Clone)]
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

impl<'a, 'b> Consume<'a, 'b> for Cmd<'a> {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("cmd");
        match parser.next(data) {
            (mut parser, Token::READ) => {
                check!(parser, data, IMAGE);
                consume!(parser, data, LiteralString, s);
                check!(parser, data, TO);
                consume!(parser, data, LValue, lvalue);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Read(s, lvalue))
            }
            (mut parser, Token::TIME) => {
                consume!(parser, data, Cmd, cmd);
                parser.complete(Self::Time(Box::new(cmd)))
            }
            (mut parser, Token::LET) => {
                consume!(parser, data, LValue, lvalue);
                check!(parser, data, EQUALS);
                consume!(parser, data, Expr, expr);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Let(lvalue, expr))
            }
            (mut parser, Token::ASSERT) => {
                consume!(parser, data, Expr, expr);
                check!(parser, data, COMMA);
                consume!(parser, data, LiteralString, s);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Assert(expr, s))
            }
            (mut parser, Token::SHOW) => {
                consume!(parser, data, Expr, expr);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Show(expr))
            }
            (mut parser, Token::WRITE) => {
                check!(parser, data, IMAGE);
                consume!(parser, data, Expr, expr);
                check!(parser, data, TO);
                consume!(parser, data, LiteralString, s);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Write(expr, s))
            }
            (mut parser, Token::PRINT) => {
                consume!(parser, data, LiteralString, s);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Print(s))
            }
            (mut parser, Token::FN) => {
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
            (mut parser, Token::TYPE) => {
                consume!(parser, data, Variable, v);
                check!(parser, data, EQUALS);
                consume!(parser, data, Type, ty);
                check!(parser, data, NEWLINE);
                parser.complete(Self::Type(v, ty))
            }
            (mut parser, Token::STRUCT) => {
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
                write!(f, "(FnCmd {name} ((",)?;
                bindings.print_joined(f, " ")?;
                write!(f, ")) {ty} ")?;
                statements.print_joined(f, " ")?;
                write!(f, ")")
            }
            Cmd::Type(name, ty) => {
                write!(f, "(TypeCmd {name} {ty})")
            }
            Cmd::Struct(name, fields) => {
                if fields.is_empty() {
                    write!(f, "(StructCmd {name})")
                } else {
                    write!(f, "(StructCmd {name} ")?;
                    fields.print_joined(f, " ")?;
                    write!(f, ")")
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
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
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("statement");
        localize_error!(parser, data, Statement<'a>, {
            match parser.first(data) {
                Token::ASSERT => {
                    parser = parser.skip_one();
                    consume!(parser, data, Expr, expr);
                    check!(parser, data, COMMA);
                    consume!(parser, data, LiteralString, msg);
                    parser.complete(Statement::Assert(expr, msg))
                }
                Token::RETURN => {
                    parser = parser.skip_one();
                    consume!(parser, data, Expr, expr);
                    parser.complete(Statement::Return(expr))
                }
                Token::LET => {
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

#[derive(Debug, Clone)]
pub enum Expr<'a> {
    // temporary
    #[allow(dead_code)]
    Int(i64, &'a str),
    Float(f64, &'a str),
    True,
    False,
    Void,
    Variable(&'a str),
    ArrayLiteral(Vec<Expr<'a>>),
    TupleLiteral(Vec<Expr<'a>>),
    Paren(Box<Expr<'a>>),
    ArrayIndex(Box<Expr<'a>>, Vec<Expr<'a>>),
    Binop(Box<Expr<'a>>, Op, Box<Expr<'a>>),
    Call(Variable<'a>, Vec<Expr<'a>>),
    TupleIndex(Box<Expr<'a>>, Vec<Expr<'a>>),
    StructLiteral(Variable<'a>, Vec<Expr<'a>>),
    Dot(Box<Expr<'a>>, Variable<'a>),
    Unop(Op, Box<Expr<'a>>),
    If(Box<Expr<'a>>, Box<Expr<'a>>, Box<Expr<'a>>),
    ArrayLoop(Vec<LoopField<'a>>, Box<Expr<'a>>),
    SumLoop(Vec<LoopField<'a>>, Box<Expr<'a>>),
}

const fn op_precedence(op: Op) -> u8 {
    match op {
        Op::Add | Op::Sub => 4,
        Op::Mul | Op::Div | Op::Mod => 5,
        Op::Less | Op::Greater | Op::LessEq | Op::GreaterEq | Op::Eq | Op::Neq => 3,
        Op::And | Op::Or => 2,
        Op::Not => u8::MAX,
    }
}

impl Expr<'_> {
    const UNOP_PRECEDENCE: u8 = 6;

    const fn precedence(&self) -> u8 {
        match self {
            Expr::TupleIndex(_, _) | Expr::ArrayIndex(_, _) => 7,
            Expr::Unop(_, _) => Self::UNOP_PRECEDENCE,
            Expr::Binop(_, op, _) => op_precedence(*op),
            Expr::If(_, _, _) | Expr::ArrayLoop(_, _) | Expr::SumLoop(_, _) => 1,
            _ => u8::MAX,
        }
    }
}

impl std::fmt::Display for Expr<'_> {
    #[allow(clippy::too_many_lines)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Int(_, i) => write!(f, "(IntExpr {})", {
                let i = i.trim_start_matches('0');
                if i.is_empty() {
                    "0"
                } else {
                    i
                }
            }),
            Expr::Float(fl, s_fl) => s_fl
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
            Expr::Variable(s) => write!(f, "(VarExpr {s})"),
            Expr::Paren(expr) => write!(f, "{expr}"),
            Expr::ArrayLiteral(exprs) => {
                if exprs.is_empty() {
                    write!(f, "(ArrayLiteralExpr)")
                } else {
                    write!(f, "(ArrayLiteralExpr ")?;
                    exprs.print_joined(f, " ")?;
                    write!(f, ")")
                }
            }
            Expr::TupleLiteral(exprs) => {
                write!(f, "(TupleLiteralExpr ")?;
                exprs.print_joined(f, " ")?;
                write!(f, ")")
            }
            Expr::ArrayIndex(s, exprs) => {
                if exprs.is_empty() {
                    write!(f, "(ArrayIndexExpr {s})")
                } else {
                    write!(f, "(ArrayIndexExpr {s} ")?;
                    exprs.print_joined(f, " ")?;
                    write!(f, ")")
                }
            }
            Expr::TupleIndex(s, exprs) => {
                write!(f, "(TupleIndexExpr {s} ")?;
                exprs.print_joined(f, " ")?;
                write!(f, ")")
            }
            Expr::Binop(expr, op, expr2) => {
                write!(f, "(BinopExpr {expr} {op} {expr2})")
            }
            Expr::Call(expr, exprs) => {
                if exprs.is_empty() {
                    write!(f, "(CallExpr {expr})")
                } else {
                    write!(f, "(CallExpr {expr} ")?;
                    exprs.print_joined(f, " ")?;
                    write!(f, ")")
                }
            }
            Expr::StructLiteral(s, exprs) => {
                if exprs.is_empty() {
                    write!(f, "(StructLiteralExpr {s})")
                } else {
                    write!(f, "(StructLiteralExpr {s} ")?;
                    exprs.print_joined(f, " ")?;
                    write!(f, ")")
                }
            }
            Expr::Dot(expr, s) => {
                write!(f, "(DotExpr {expr} {s})")
            }
            Expr::Unop(op, expr) => {
                write!(f, "(UnopExpr {op} {expr})")
            }
            Expr::If(expr, expr2, expr3) => {
                write!(f, "(IfExpr {expr} {expr2} {expr3})")
            }
            Expr::ArrayLoop(fields, expr) => {
                if fields.is_empty() {
                    write!(f, "(ArrayLoopExpr {expr})")
                } else {
                    write!(f, "(ArrayLoopExpr ")?;
                    fields.print_joined(f, " ")?;
                    write!(f, " {expr})")
                }
            }
            Expr::SumLoop(fields, expr) => {
                if fields.is_empty() {
                    write!(f, "(SumLoopExpr {expr})")
                } else {
                    write!(f, "(SumLoopExpr ")?;
                    fields.print_joined(f, " ")?;
                    write!(f, " {expr})")
                }
            }
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Expr<'a> {
    #[allow(clippy::too_many_lines)]
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("expr");
        let (mut parser, mut expr) = match parser.next(data) {
            (mut parser, Token::OP(op @ (Op::Not | Op::Sub))) => {
                fn rearrange_according_to_precedence(
                    op: Op,
                    right_expr: Expr<'_>,
                ) -> Expr<'_> {
                    if Expr::UNOP_PRECEDENCE < right_expr.precedence() {
                        Expr::Unop(op, Box::new(right_expr))
                    } else {
                        match right_expr {
                            Expr::Binop(right_expr_left, c2, right_expr_right) => Expr::Binop(
                                Box::new(rearrange_according_to_precedence(
                                    op,
                                    *right_expr_left,
                                )),
                                c2,
                                right_expr_right,
                            ),
                            expr => Expr::Unop(op, Box::new(expr)),
                        }
                    }
                }

                consume!(parser, data, Expr, expr);
                (parser, rearrange_according_to_precedence(op, expr))
            }
            (parser, Token::INTVAL(s)) => {
                if let Ok(i) = s.parse::<i64>() {
                    (parser, Expr::Int(i, s))
                } else {
                    miss!(parser, "couldn't parse integer {s}")
                }
            }
            (parser, Token::FLOATVAL(s)) => {
                if let Ok(f) = s.parse::<f64>() {
                    if !f.is_finite() {
                        miss!(parser, "expected a finite float, found {f}");
                    }

                    (parser, Expr::Float(f, s))
                } else {
                    miss!(parser, "couldn't parse float {s}")
                }
            }
            (parser, Token::VOID) => (parser, Expr::Void),
            (parser, Token::TRUE) => (parser, Expr::True),
            (parser, Token::FALSE) => (parser, Expr::False),
            (parser, Token::VARIABLE(s)) => (parser, Expr::Variable(s)),
            (mut parser, Token::LSQUARE) => {
                consume_list!(parser, data, RSQUARE, exprs);
                (parser, Expr::ArrayLiteral(exprs))
            }
            (mut parser, Token::LPAREN) => {
                consume!(parser, data, Expr, expr);
                check!(parser, data, RPAREN);
                (parser, Expr::Paren(Box::new(expr)))
            }
            (mut parser, Token::LCURLY) => {
                consume_list!(parser, data, RCURLY, exprs);
                (parser, Expr::TupleLiteral(exprs))
            }
            (mut parser, Token::IF) => {
                consume!(parser, data, Expr, expr);
                check!(parser, data, THEN);
                consume!(parser, data, Expr, expr2);
                check!(parser, data, ELSE);
                consume!(parser, data, Expr, expr3);
                (parser, Expr::If(Box::new(expr), Box::new(expr2), Box::new(expr3)))
            }
            (mut parser, Token::ARRAY) => {
                check!(parser, data, LSQUARE);
                consume_list!(parser, data, RSQUARE, fields);
                consume!(parser, data, Expr, expr);
                (parser, Expr::ArrayLoop(fields, Box::new(expr)))
            }
            (mut parser, Token::SUM) => {
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
            let (rem_parser, new_expr) = match (parser.next(data), &expr) {
                ((mut parser, Token::LSQUARE), _) => {
                    consume_list!(parser, data, RSQUARE, exprs);
                    (parser, Expr::ArrayIndex(Box::new(expr), exprs))
                }
                ((mut parser, Token::LPAREN), Expr::Variable(s)) => {
                    consume_list!(parser, data, RPAREN, exprs);
                    (parser, Expr::Call(Variable(s), exprs))
                }
                ((mut parser, Token::LCURLY), Expr::Variable(s)) => {
                    consume_list!(parser, data, RCURLY, exprs);
                    (parser, Expr::StructLiteral(Variable(s), exprs))
                }
                ((mut parser, Token::LCURLY), _) => {
                    consume_list!(parser, data, RCURLY, exprs);
                    (parser, Expr::TupleIndex(Box::new(expr), exprs))
                }
                ((mut parser, Token::DOT), _) => {
                    consume!(parser, data, Variable, var);
                    (parser, Expr::Dot(Box::new(expr), var))
                }
                ((mut parser, Token::OP(op)), _) => {
                    fn rearrange_according_to_precedence<'a>(
                        new_expr: Expr<'a>,
                        op: Op,
                        right_expr: Expr<'a>,
                    ) -> Expr<'a> {
                        if op_precedence(op) < right_expr.precedence() {
                            Expr::Binop(Box::new(new_expr), op, Box::new(right_expr))
                        } else {
                            match right_expr {
                                Expr::Binop(right_expr_left, c2, right_expr_right) => Expr::Binop(
                                    Box::new(rearrange_according_to_precedence(
                                        new_expr,
                                        op,
                                        *right_expr_left,
                                    )),
                                    c2,
                                    right_expr_right,
                                ),
                                _ => Expr::Binop(Box::new(new_expr), op, Box::new(right_expr)),
                            }
                        }
                    }

                    consume!(parser, data, Expr, expr2);
                    (parser, rearrange_according_to_precedence(expr, op, expr2))
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
                write!(f, "(ArrayLValue {s} ")?;
                args.print_joined(f, " ")?;
                write!(f, ")")
            }
            LValue::Tuple(lvs) => {
                write!(f, "(TupleLValue ")?;
                lvs.print_joined(f, " ")?;
                write!(f, ")")
            }
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for LValue<'a> {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("lvalue");
        let (parser, lv) = match parser.next(data) {
            (parser, Token::VARIABLE(s)) => (parser, LValue::Var(Variable(s))),
            (mut parser, Token::LCURLY) => {
                consume_list!(parser, data, RCURLY, lvs);
                (parser, LValue::Tuple(lvs))
            }
            (_, t) => miss!(
                parser,
                "expected start of lvalue (VARIABLE | LCURLY), found {t:?}"
            ),
        };

        let (parser, lv) = match (parser.next(data), &lv) {
            ((mut parser, Token::LSQUARE), &LValue::Var(s)) => {
                consume_list!(parser, data, RSQUARE, args);
                (parser, LValue::Array(s, args))
            }
            _ => (parser, lv),
        };

        parser.complete(lv)
    }
}

#[derive(Debug, Clone)]
pub enum Type<'a> {
    Struct(&'a str),
    Array(Box<Type<'a>>, u8),
    Float,
    Int,
    Bool,
    Void,
    Tuple(Vec<Type<'a>>),
}

impl PartialEq for Type<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Struct(s), Type::Struct(o)) => s.as_ptr() == o.as_ptr(),
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
                write!(f, "(TupleType ")?;
                tys.print_joined(f, " ")?;
                write!(f, ")")
            }
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Type<'a> {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("type");
        let (mut parser, mut ty) = match parser.next(data) {
            (parser, Token::VARIABLE(s)) => (parser, Type::Struct(s)),
            (parser, Token::INT) => (parser, Type::Int),
            (parser, Token::BOOL) => (parser, Type::Bool),
            (parser, Token::VOID) => (parser, Type::Void),
            (parser, Token::FLOAT) => (parser, Type::Float),
            (mut parser, Token::LCURLY) => {
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
            match (parser.first(data), &ty) {
                (Token::LSQUARE, _) => {
                    parser = parser.skip_one();

                    let mut depth: u8 = 1;

                    loop {
                        match parser.next(data) {
                            (advanced_parser, Token::RSQUARE) => {
                                parser = advanced_parser;
                                break;
                            }
                            (advanced_parser, Token::COMMA) => {
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

impl<'a, 'b> Consume<'a, 'b> for Binding<'a> {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self> {
        measure!("binding");
        localize_error!(parser, data, Binding<'a>, {
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
    tokens: &'a [Token<'a>],
    input_by_token: &'a [&'a str],
    source: &'a str,
    path: &'a Path,
) -> Result<Vec<Cmd<'a>>> {
    measure!("parse");
    let mut cmds = vec![];

    let mut parser = Parser {
        current_position: 0,
    };

    let data = StaticParserData {
        original_tokens: tokens,
        input_by_token,
        source,
    };

    // let data = unsafe { &*std::ptr::from_ref::<StaticParserData<'a>>(&data) };
    let data = &data;

    while !parser.is_empty(data) {
        let cmd = Cmd::consume(parser, data);

        match cmd {
            ParseResult::Parsed(moved_parser, cmd) => {
                // debug_assert_ne!(moved_parser, parser);
                parser = moved_parser;

                let cmd: Cmd<'a> = cmd;

                cmds.push(cmd);
            }
            pr => {
                if let Token::NEWLINE = parser.first(data) {
                    parser = parser.skip_one();
                    continue;
                }

                if let Token::END_OF_FILE = parser.first(data) {
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
        let (tokens, input_by_token) = crate::lex::LexNom::lex(file).expect("Lexing should work");

        let parsed = match parse(&tokens, &input_by_token, file, Path::new("")) {
            Ok(parsed) => parsed,
            Err(e) => {
                panic!("Compilation failed {e}");
            }
        };

        let mut output = String::new();

        for parsed in parsed {
            use std::fmt::Write;
            writeln!(output, "{parsed}").unwrap();
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
        let Ok((tokens, input_by_tokens)) = crate::lex::LexNom::lex(file) else {
            return;
        };

        match parse(&tokens, &input_by_tokens, file, file_path) {
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
