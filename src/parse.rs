use std::{fmt::Write, path::Path};

use anyhow::{bail, Result};
use parser::{
    check, consume, consume_list, consume_list_impl, localize_error, miss, Consume, ParseResult,
    Parser, StaticParserData,
};

use crate::{
    lex::{Token, TokenType},
    measure,
};

mod parser;
mod printing;
#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy)]
pub struct Variable(usize);

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

#[derive(Debug, Clone)]
pub enum Statement {
    Let(LValue, Expr),
    Assert(Expr, LiteralString),
    Return(Expr),
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

        while let (TokenType::LSQUARE, _) = (parser.first_type(data), &ty) {
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

        parser.complete(ty)
    }
}

#[derive(Debug, Clone)]
pub enum Binding {
    Var(LValue, Type),
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
