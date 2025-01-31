use color_eyre::eyre::{bail, Result};
use colored::Colorize;
use itertools::Itertools;

use crate::{
    lex::{Op, Token},
    undo_slice_by_cuts, UndoSliceSelection,
};

#[cfg(test)]
use crate::lex::LexImplementation;
#[cfg(test)]
use crate::{test_correct, test_solos};

trait Consume<'a>: Sized {
    fn consume(tokens: Parser<'a>) -> ParseResult<'a, Self>;
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
    NotParsed(Box<dyn Fn() -> String + 'a>, usize),
    Parsed(Parser<'a>, T),
}

macro_rules! miss {
    ($parser:ident, $($msg:tt)*) => {
        return $parser.miss(Box::new(move || format!($($msg)*)))
    };
}

macro_rules! consume {
    ($parser:ident, $type:ty, $outvar:ident) => {
        let (advanced_parser, $outvar) = match <$type>::consume($parser) {
            ParseResult::NotParsed(report, position) => {
                return ParseResult::NotParsed(report, position)
            }
            ParseResult::Parsed(parser, t) => {
                debug_assert_ne!($parser, parser);
                (parser, t)
            }
        };

        $parser = advanced_parser;
    };
}

fn consume_list<'a, 'b, T: Consume<'a> + std::fmt::Debug>(
    mut parser: Parser<'a>,
    end_token: Token<'a>,
    delimeter: Token<'a>,
    delimeter_terminated: bool,
) -> ParseResult<'a, Vec<T>> {
    let mut list = vec![];
    loop {
        if let ParseResult::Parsed(parser, _) = parser.check_skip(end_token) {
            return parser.complete(list);
        }

        consume!(parser, T, t);
        list.push(t);

        match parser.first() {
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
    ($parser:ident, $end_token:tt, $delimeter:tt, $delimeter_terminated:expr, $outvar:ident) => {
        let (advanced_parser, $outvar) = match consume_list(
            $parser,
            Token::$end_token,
            Token::$delimeter,
            $delimeter_terminated,
        ) {
            ParseResult::NotParsed(report, position) => {
                return ParseResult::NotParsed(report, position)
            }
            ParseResult::Parsed(parser, t) => {
                debug_assert_ne!($parser, parser);
                (parser, t)
            }
        };

        $parser = advanced_parser;
    };
    ($parser:ident, $end_token:tt, $delimeter:tt, $outvar:ident) => {
        consume_list!($parser, $end_token, $delimeter, false, $outvar)
    };
    ($parser:ident, $end_token:tt, $outvar:ident) => {
        consume_list!($parser, $end_token, COMMA, false, $outvar)
    };
}

macro_rules! check {
    ($parser:ident, $token:tt) => {
        let advanced_parser = match $parser.check_skip(Token::$token) {
            ParseResult::NotParsed(report, position) => {
                return ParseResult::NotParsed(report, position)
            }
            ParseResult::Parsed(parser, _) => (parser),
        };

        $parser = advanced_parser;
    };
}

#[derive(Debug, Clone, Copy)]
struct Parser<'a> {
    original_tokens: &'a [Token<'a>],
    current_position: usize,
    input_by_token: &'a [&'a str],
    source: &'a str,
}

impl PartialEq for Parser<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.current_position == other.current_position
    }
}

impl<'a> Parser<'a> {
    fn complete<T>(&self, t: T) -> ParseResult<'a, T> {
        ParseResult::Parsed(*self, t)
    }

    fn miss<T>(&self, report: Box<dyn Fn() -> String + 'a>) -> ParseResult<'a, T> {
        ParseResult::NotParsed(report, self.current_position)
    }

    #[must_use]
    fn skip_one(mut self) -> Self {
        self.current_position += 1;
        self
    }

    fn check_skip(self, token: Token<'a>) -> ParseResult<'a, ()> {
        debug_assert_ne!(token, Token::END_OF_FILE);
        if self.check_one(token) {
            ParseResult::Parsed(self.skip_one(), ())
        } else {
            ParseResult::NotParsed(
                Box::new(move || format!("expected {token:?}, found {:?}", self.first())),
                self.current_position,
            )
        }
    }

    fn check_one(&self, token: Token<'a>) -> bool {
        self.first() == token
    }

    fn first(&self) -> Token<'a> {
        debug_assert!(self.original_tokens.get(self.current_position).is_some());
        // SAFETY: EOF is always at the end and we never check for EOF
        unsafe { *self.original_tokens.get_unchecked(self.current_position) }
    }

    fn next(self) -> (Self, Token<'a>) {
        let next = self.first();
        (self.skip_one(), next)
    }

    fn is_empty(&self) -> bool {
        self.current_position == self.original_tokens.len()
    }

    /// This function prints the error token text in red and the surrounding text.
    fn print_error(&self, error_position: usize) {
        let current_position = self.current_position;

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

            (source_pre, src_iter.count()..)
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

        let output = format!("{}{}{}{}", source_pre, semi_valid, error, source_post);
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

        for (line_number, line) in output {
            println!(
                "{}{line}",
                format!("{line_number:>max_length_of_line_number$} | ").bright_blue()
            );
        }
        println!();
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Variable<'a>(&'a str);

impl std::fmt::Display for Variable<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}

impl<'a> Consume<'a> for Variable<'a> {
    fn consume(parser: Parser<'a>) -> ParseResult<'a, Self> {
        let (parser, s) = match parser.next() {
            (parser, Token::VARIABLE(s)) => (parser, s),
            t => miss!(parser, "expected variable, found {t:?}"),
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

impl<'a> Consume<'a> for LiteralString<'a> {
    fn consume(parser: Parser<'a>) -> ParseResult<'a, Self> {
        let s = match parser.first() {
            Token::STRING(s) => s,
            t => miss!(parser, "expected string, found {t:?}"),
        };

        parser.skip_one().complete(Self(s))
    }
}

#[derive(Debug, Clone)]
pub struct Field<'a>(Variable<'a>, Type<'a>);

impl std::fmt::Display for Field<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.0, self.1)
    }
}

impl<'a> Consume<'a> for Field<'a> {
    fn consume(mut parser: Parser<'a>) -> ParseResult<'a, Self> {
        consume!(parser, Variable, s);
        check!(parser, COLON);
        consume!(parser, Type, ty);
        parser.complete(Self(s, ty))
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

impl<'a> Consume<'a> for Cmd<'a> {
    fn consume(parser: Parser<'a>) -> ParseResult<'a, Self> {
        match parser.next() {
            (mut parser, Token::READ) => {
                check!(parser, IMAGE);
                consume!(parser, LiteralString, s);
                check!(parser, TO);
                consume!(parser, LValue, lvalue);
                check!(parser, NEWLINE);
                parser.complete(Self::Read(s, lvalue))
            }
            (mut parser, Token::TIME) => {
                consume!(parser, Cmd, cmd);
                parser.complete(Self::Time(Box::new(cmd)))
            }
            (mut parser, Token::LET) => {
                consume!(parser, LValue, lvalue);
                check!(parser, EQUALS);
                consume!(parser, Expr, expr);
                check!(parser, NEWLINE);
                parser.complete(Self::Let(lvalue, expr))
            }
            (mut parser, Token::ASSERT) => {
                consume!(parser, Expr, expr);
                check!(parser, COMMA);
                consume!(parser, LiteralString, s);
                check!(parser, NEWLINE);
                parser.complete(Self::Assert(expr, s))
            }
            (mut parser, Token::SHOW) => {
                consume!(parser, Expr, expr);
                check!(parser, NEWLINE);
                parser.complete(Self::Show(expr))
            }
            (mut parser, Token::WRITE) => {
                check!(parser, IMAGE);
                consume!(parser, Expr, expr);
                check!(parser, TO);
                consume!(parser, LiteralString, s);
                check!(parser, NEWLINE);
                parser.complete(Self::Write(expr, s))
            }
            (mut parser, Token::PRINT) => {
                consume!(parser, LiteralString, s);
                check!(parser, NEWLINE);
                parser.complete(Self::Print(s))
            }
            (mut parser, Token::FN) => {
                consume!(parser, Variable, v);
                check!(parser, LPAREN);
                consume_list!(parser, RPAREN, bindings);
                check!(parser, COLON);
                consume!(parser, Type, ty);
                check!(parser, LCURLY);
                check!(parser, NEWLINE);
                consume_list!(parser, RCURLY, NEWLINE, true, statements);
                parser.complete(Self::Fn(v, bindings, ty, statements))
            }
            (mut parser, Token::TYPE) => {
                consume!(parser, Variable, v);
                check!(parser, EQUALS);
                consume!(parser, Type, ty);
                check!(parser, NEWLINE);
                parser.complete(Self::Type(v, ty))
            }
            (mut parser, Token::STRUCT) => {
                consume!(parser, Variable, v);
                check!(parser, LCURLY);
                check!(parser, NEWLINE);
                consume_list!(parser, RCURLY, NEWLINE, fields);
                parser.complete(Self::Struct(v, fields))
            }
            t => miss!(parser, "expected a command keyword (ASSERT | RETURN | LET | ASSERT | PRINT | SHOW | TIME | FN | TYPE | STRUCT), found {t:?}"),
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

impl<'a> Consume<'a> for Statement<'a> {
    fn consume(mut parser: Parser<'a>) -> ParseResult<'a, Self> {
        match parser.first() {
            Token::ASSERT => {
                parser = parser.skip_one();
                consume!(parser, Expr, expr);
                check!(parser, COMMA);
                consume!(parser, LiteralString, msg);
                parser.complete(Self::Assert(expr, msg))
            }
            Token::RETURN => {
                parser = parser.skip_one();
                consume!(parser, Expr, expr);
                parser.complete(Self::Return(expr))
            }
            Token::LET => {
                parser = parser.skip_one();
                consume!(parser, LValue, lvalue);
                check!(parser, EQUALS);
                consume!(parser, Expr, expr);
                parser.complete(Self::Let(lvalue, expr))
            }
            t => miss!(
                parser,
                "expected a start of statement (ASSERT | RETURN | LET), found {t:?}"
            ),
        }
    }
}

#[derive(Debug, Clone)]
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
                if exprs.is_empty() {
                    write!(f, "(ArrayLiteralExpr)")
                } else {
                    write!(f, "(ArrayLiteralExpr ")?;
                    exprs.print_joined(f, " ")?;
                    write!(f, ")")
                }
            }
            Expr::Tuple(exprs) => {
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
        }
    }
}

impl<'a> Consume<'a> for Expr<'a> {
    fn consume(parser: Parser<'a>) -> ParseResult<'a, Self> {
        let (mut parser, mut expr) = match parser.next() {
            (parser, Token::INTVAL(s)) => {
                if let Ok(i) = s.parse::<i64>() {
                    (parser, Expr::Int(i))
                } else {
                    miss!(parser, "couldn't parse integer {s}")
                }
            }
            (parser, Token::FLOATVAL(s)) => {
                if let Ok(f) = s.parse::<f64>() {
                    if !f.is_finite() {
                        miss!(parser, "expected a finite float, found {f}");
                    }

                    (parser, Expr::Float(f))
                } else {
                    miss!(parser, "couldn't parse float {s}")
                }
            }
            (parser, Token::VOID) => (parser, Expr::Void),
            (parser, Token::TRUE) => (parser, Expr::True),
            (parser, Token::FALSE) => (parser, Expr::False),
            (parser, Token::VARIABLE(s)) => (parser, Expr::Variable(s)),
            (mut parser, Token::LSQUARE) => {
                consume_list!(parser, RSQUARE, exprs);
                (parser, Expr::Array(exprs))
            }
            (mut parser, Token::LPAREN) => {
                consume!(parser, Expr, expr);
                check!(parser, RPAREN);
                (parser, expr)
            }
            (mut parser, Token::LCURLY) => {
                consume_list!(parser, RCURLY, exprs);
                (parser, Expr::Tuple(exprs))
            }
            t => miss!(parser,
                "expected start of expression (INTVAL | FLOATVAL | TRUE | FALSE | VARIABLE | LSQUARE | LPAREN | LCURLY), found {t:?}"
            ),
        };

        let (parser, expr) = loop {
            let (rem_parser, new_expr) = match (parser.next(), &expr) {
                ((mut parser, Token::LSQUARE), _) => {
                    consume_list!(parser, RSQUARE, exprs);
                    (parser, Expr::ArrayIndex(Box::new(expr), exprs))
                }
                ((mut parser, Token::LPAREN), Expr::Variable(s)) => {
                    consume_list!(parser, RPAREN, exprs);
                    (parser, Expr::Call(Variable(s), exprs))
                }
                ((mut parser, Token::LCURLY), Expr::Variable(s)) => {
                    consume_list!(parser, RCURLY, exprs);
                    (parser, Expr::StructLiteral(Variable(s), exprs))
                }
                ((mut parser, Token::LCURLY), _) => {
                    consume_list!(parser, RCURLY, exprs);
                    (parser, Expr::TupleIndex(Box::new(expr), exprs))
                }
                ((mut parser, Token::DOT), _) => {
                    consume!(parser, Variable, var);
                    (parser, Expr::Dot(Box::new(expr), var))
                }
                _ => break (parser, expr),
            };
            parser = rem_parser;
            expr = new_expr;
        };

        // let (parser, expr) = match parser.first() {
        //     // // ? Only Eq right now to pass that bad test
        //     // Some(Token::OP(c @ Op::Eq)) => {
        //     //     parser.skip_one();
        //     //     let (parser, expr2) = Expr::consume(parser).wrap_err("parsing binary op expr")?;
        //     //     (parser, Expr::Binop(Box::new(expr), c, Box::new(expr2)))
        //     // }
        //     _ => (parser, expr),
        // };

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

impl<'a> Consume<'a> for LValue<'a> {
    fn consume(parser: Parser<'a>) -> ParseResult<'a, Self> {
        let (parser, lv) = match parser.next() {
            (parser, Token::VARIABLE(s)) => (parser, LValue::Var(Variable(s))),
            (mut parser, Token::LCURLY) => {
                consume_list!(parser, RCURLY, lvs);
                (parser, LValue::Tuple(lvs))
            }
            t => miss!(
                parser,
                "expected start of lvalue (VARIABLE | LCURLY), found {t:?}"
            ),
        };

        let (parser, lv) = match (parser.next(), &lv) {
            ((mut parser, Token::LSQUARE), &LValue::Var(s)) => {
                consume_list!(parser, RSQUARE, args);
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
            (Type::Float, Type::Float) => true,
            (Type::Int, Type::Int) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::Void, Type::Void) => true,
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

impl<'a> Consume<'a> for Type<'a> {
    fn consume(parser: Parser<'a>) -> ParseResult<'a, Self> {
        let (mut parser, mut ty) = match parser.next() {
            (parser, Token::VARIABLE(s)) => (parser, Type::Struct(s)),
            (parser, Token::INT) => (parser, Type::Int),
            (parser, Token::BOOL) => (parser, Type::Bool),
            (parser, Token::VOID) => (parser, Type::Void),
            (parser, Token::FLOAT) => (parser, Type::Float),
            (mut parser, Token::LCURLY) => {
                consume_list!(parser, RCURLY, tys);
                (parser, Type::Tuple(tys))
            }
            t => miss!(
                parser,
                "expected start of type (VARIABLE | FLOAT | LCURLY), found {t:?}"
            ),
        };

        #[allow(clippy::while_let_loop)]
        loop {
            match (parser.first(), &ty) {
                (Token::LSQUARE, _) => {
                    parser = parser.skip_one();

                    let mut depth: u8 = 1;

                    loop {
                        match parser.next() {
                            (advanced_parser, Token::RSQUARE) => {
                                parser = advanced_parser;
                                break;
                            }
                            (advanced_parser, Token::COMMA) => {
                                parser = advanced_parser;
                                depth += 1;
                            }
                            t => miss!(parser, "expected RSQUARE or COMMA, found {t:?}"),
                        }
                    }

                    ty = Self::Array(Box::new(ty), depth)
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

impl<'a> Consume<'a> for Binding<'a> {
    fn consume(mut parser: Parser<'a>) -> ParseResult<'a, Self> {
        consume!(parser, LValue, lv);
        check!(parser, COLON);
        consume!(parser, Type, ty);
        parser.complete(Self::Var(lv, ty))
    }
}

pub fn parse<'a>(
    tokens: &'a [Token<'a>],
    input_by_token: &'a [&'a str],
    source: &'a str,
) -> Result<Vec<Cmd<'a>>> {
    let mut cmds = vec![];

    let mut parser = Parser {
        original_tokens: tokens,
        current_position: 0,
        input_by_token,
        source,
    };

    while !parser.is_empty() {
        let cmd = Cmd::consume(parser);

        match cmd {
            ParseResult::Parsed(moved_parser, cmd) => {
                // debug_assert_ne!(moved_parser, parser);
                parser = moved_parser;
                // parser.successfully_parsed.set(0);
                cmds.push(cmd);
            }
            ParseResult::NotParsed(e, err_position) => {
                if let Token::NEWLINE = parser.first() {
                    parser = parser.skip_one();
                    continue;
                }

                if let Token::END_OF_FILE = parser.first() {
                    break;
                }

                parser.print_error(err_position);

                bail!("{}", e());
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
        let Ok((tokens, input_by_tokens)) = crate::lex::LexNom::lex(file.unwrap()) else {
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
