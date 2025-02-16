use std::{fmt::Write, path::Path};

use anyhow::{bail, Result};
use parser::{
    check, consume, consume_list, consume_list_impl, localize_error, miss, Consume, ParseResult,
    Parser, ParserContext,
};

use crate::{
    lex::{Token, TokenType},
    measure,
};

pub use parser::SourceInfo;

mod parser;
mod printing;
#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy)]
pub struct Variable(pub usize, pub SourceInfo);

impl<'a, 'b> Consume<'a, 'b> for Variable {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("variable");
        let (parser, s, source_info) = match parser.next(ctx) {
            (parser, t, source_info) if t.get_type() == TokenType::VARIABLE => {
                (parser, t.get_index(), source_info)
            }
            (_, t, _) => miss!(parser, "expected variable, found {:?}", t),
        };

        parser.complete(Self(s, source_info), source_info)
    }
}

impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LiteralString(usize, SourceInfo);

impl<'a, 'b> Consume<'a, 'b> for LiteralString {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("string_lit");
        let (s, source_info) = match parser.first(ctx) {
            (t, source_info) if t.get_type() == TokenType::STRING => (t.get_index(), source_info),
            t => miss!(parser, "expected string, found {t:?}"),
        };

        parser
            .skip_one()
            .complete(Self(s, source_info), source_info)
    }
}

impl PartialEq for LiteralString {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

#[derive(Debug, Clone)]
pub struct LoopField(pub Variable, pub Expr);

impl<'a, 'b> Consume<'a, 'b> for LoopField {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("arraySumField");
        localize_error!(parser, ctx, LoopField, {
            let range = SourceInfo::mark_range(&parser);
            consume!(parser, ctx, Variable, s);
            check!(parser, ctx, COLON);
            consume!(parser, ctx, Expr, expr);

            parser.complete_range(LoopField(s, expr), &range)
        })
    }
}

#[derive(Debug, Clone)]
pub struct Field(pub Variable, pub Type);

impl<'a, 'b> Consume<'a, 'b> for Field {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("field");
        localize_error!(parser, ctx, Field, {
            let range = SourceInfo::mark_range(&parser);
            consume!(parser, ctx, Variable, s);
            check!(parser, ctx, COLON);
            consume!(parser, ctx, Type, ty);
            parser.complete_range(Field(s, ty), &range)
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
    Struct(Variable, Vec<Field>),
}

impl<'a, 'b> Consume<'a, 'b> for Cmd {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("cmd");
        let range = SourceInfo::mark_range(&parser);
        let (parser, cmd) = match parser.next_type(ctx) {
            (mut parser, TokenType::READ)=> {
                check!(parser, ctx, IMAGE);
                consume!(parser, ctx, LiteralString, s);
                check!(parser, ctx, TO);
                consume!(parser, ctx, LValue, lvalue);
                check!(parser, ctx, NEWLINE);
                (parser, Self::Read(s, lvalue))
            }
            (mut parser, TokenType::TIME)=> {
                consume!(parser, ctx, Cmd, cmd);
                (parser, Self::Time(Box::new(cmd)))
            }
            (mut parser, TokenType::LET)=> {
                consume!(parser, ctx, LValue, lvalue);
                check!(parser, ctx, EQUALS);
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, NEWLINE);
                (parser, Self::Let(lvalue, expr))
            }
            (mut parser, TokenType::ASSERT)=> {
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, COMMA);
                consume!(parser, ctx, LiteralString, s);
                check!(parser, ctx, NEWLINE);
                (parser, Self::Assert(expr, s))
            }
            (mut parser, TokenType::SHOW)=> {
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, NEWLINE);
                (parser, Self::Show(expr))
            }
            (mut parser, TokenType::WRITE)=> {
                check!(parser, ctx, IMAGE);
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, TO);
                consume!(parser, ctx, LiteralString, s);
                check!(parser, ctx, NEWLINE);
                (parser, Self::Write(expr, s))
            }
            (mut parser, TokenType::PRINT)=> {
                consume!(parser, ctx, LiteralString, s);
                check!(parser, ctx, NEWLINE);
                (parser, Self::Print(s))
            }
            (mut parser, TokenType::FN)=> {
                consume!(parser, ctx, Variable, v);
                check!(parser, ctx, LPAREN);
                consume_list!(parser, ctx, RPAREN, bindings);
                check!(parser, ctx, COLON);
                consume!(parser, ctx, Type, ty);
                check!(parser, ctx, LCURLY);
                check!(parser, ctx, NEWLINE);
                consume_list!(parser, ctx, RCURLY, NEWLINE, true, statements);
                (parser, Self::Fn(v, bindings, ty, statements))
            }
            (mut parser, TokenType::STRUCT)=> {
                consume!(parser, ctx, Variable, v);
                check!(parser, ctx, LCURLY);
                check!(parser, ctx, NEWLINE);
                consume_list!(parser, ctx, RCURLY, NEWLINE, fields);
                (parser, Self::Struct(v, fields))
            }
            (_, t)=> miss!(parser, "expected a command keyword (ASSERT | RETURN | LET | ASSERT | PRINT | SHOW | TIME | FN | TYPE | STRUCT), found {t:?}"),
        };

        parser.complete_range(cmd, &range)
    }
}

#[derive(Debug, Clone)]
pub enum Statement {
    Let(LValue, Expr),
    Assert(Expr, LiteralString),
    Return(Expr),
}

impl<'a, 'b> Consume<'a, 'b> for Statement {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("statement");

        localize_error!(parser, ctx, Statement, {
            let range = SourceInfo::mark_range(&parser);
            match parser.first_type(ctx) {
                TokenType::ASSERT => {
                    parser = parser.skip_one();
                    consume!(parser, ctx, Expr, expr);
                    check!(parser, ctx, COMMA);
                    consume!(parser, ctx, LiteralString, msg);
                    parser.complete_range(Statement::Assert(expr, msg), &range)
                }
                TokenType::RETURN => {
                    parser = parser.skip_one();
                    consume!(parser, ctx, Expr, expr);
                    parser.complete_range(Statement::Return(expr), &range)
                }
                TokenType::LET => {
                    parser = parser.skip_one();
                    consume!(parser, ctx, LValue, lvalue);
                    check!(parser, ctx, EQUALS);
                    consume!(parser, ctx, Expr, expr);
                    parser.complete_range(Statement::Let(lvalue, expr), &range)
                }
                t => miss!(
                    parser,
                    "expected a start of statement (ASSERT | RETURN | LET), found {t:?}"
                ),
            }
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Op(pub TokenType);

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
    Int(i64, usize, SourceInfo),
    Float(f64, usize, SourceInfo),
    True(SourceInfo),
    False(SourceInfo),
    Void(SourceInfo),
    Paren(Box<Expr>),
    // Typed
    Variable(Variable, Type),
    ArrayLiteral(Vec<Expr>, Type),
    ArrayIndex(Box<Expr>, Vec<Expr>, Type),
    Binop(Box<Expr>, Op, Box<Expr>, Type),
    Call(Variable, Vec<Expr>, Type),
    StructLiteral(Variable, Vec<Expr>, Type),
    Dot(Box<Expr>, Variable, Type),
    Unop(Op, Box<Expr>, Type),
    If(Box<Expr>, Box<Expr>, Box<Expr>, Type),
    ArrayLoop(Vec<LoopField>, Box<Expr>, Type),
    SumLoop(Vec<LoopField>, Box<Expr>, Type),
}

impl Expr {
    const UNOP_PRECEDENCE: u8 = 6;

    const fn precedence(&self) -> u8 {
        match self {
            Expr::ArrayIndex(_, _, _) => 7,
            Expr::Unop(_, _, _) => Self::UNOP_PRECEDENCE,
            Expr::Binop(_, op, _, _) => op.precedence(),
            Expr::If(_, _, _, _) | Expr::ArrayLoop(_, _, _) | Expr::SumLoop(_, _, _) => 1,
            _ => u8::MAX,
        }
    }

    #[must_use]
    pub fn get_type(&self) -> Type {
        match self {
            Expr::Int(_, _, _) => Type::Int,
            Expr::Float(_, _, _) => Type::Float,
            Expr::Void(_) => Type::Void,
            Expr::True(_) | Expr::False(_) => Type::Bool,
            Expr::Paren(expr) => expr.get_type(),
            Expr::ArrayLiteral(_, ty)
            | Expr::StructLiteral(_, _, ty)
            | Expr::ArrayLoop(_, _, ty)
            | Expr::SumLoop(_, _, ty)
            | Expr::Dot(_, _, ty)
            | Expr::Binop(_, _, _, ty)
            | Expr::Unop(_, _, ty)
            | Expr::Variable(_, ty)
            | Expr::Call(_, _, ty)
            | Expr::If(_, _, _, ty)
            | Expr::ArrayIndex(_, _, ty) => ty.clone(),
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Expr {
    #[allow(clippy::too_many_lines)]
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("expr");
        let next = parser.next(ctx);
        let range = SourceInfo::mark_range(&parser);
        let (mut parser, mut expr) = match (next.0, next.1.get_type(), next.2) {
            (mut parser, op @ (TokenType::Not | TokenType::Sub), _) => {
                measure!("unop");
                fn rearrange_according_to_precedence(
                    op: Op,
                    right_expr: Expr,
                ) -> Expr {
                    if Expr::UNOP_PRECEDENCE < right_expr.precedence() {
                        Expr::Unop(op, Box::new(right_expr), Type::None)
                    } else {
                        match right_expr {
                            Expr::Binop(mut right_expr_left, c2, right_expr_right, _) => Expr::Binop(
                                {
                                    // reuxe the allocation from right_expr_left 
                                    *right_expr_left = rearrange_according_to_precedence(op,*right_expr_left);
                                    right_expr_left
                                },
                                c2,
                                right_expr_right,
                                Type::None,
                            ),
                            expr => Expr::Unop(op, Box::new(expr), Type::None),
                        }
                    }
                }

                consume!(parser, ctx, Expr, expr);
                (parser, rearrange_according_to_precedence(op.into(), expr))
            }
            (parser, TokenType::INTVAL, source_info) => {
                let si = next.1.get_index();
                let s = ctx.string_map[si];
                if let Ok(i) = s.parse::<i64>() {
                    (parser, Expr::Int(i, si, source_info))
                } else {
                    miss!(parser, "couldn't parse integer {s}")
                }
            }
            (parser, TokenType::FLOATVAL, source_info) => {
                let si = next.1.get_index();
                let s = ctx.string_map[si];
                if let Ok(f) = s.parse::<f64>() {
                    if !f.is_finite() {
                        miss!(parser, "expected a finite float, found {f}");
                    }

                    (parser, Expr::Float(f, si, source_info))
                } else {
                    miss!(parser, "couldn't parse float {s}")
                }
            }
            (parser, TokenType::VOID, source_info) => (parser, Expr::Void(source_info)),
            (parser, TokenType::TRUE, source_info) => (parser, Expr::True(source_info)),
            (parser, TokenType::FALSE, source_info) => (parser, Expr::False(source_info)),
            (parser, TokenType::VARIABLE, source_info) => (parser, Expr::Variable(Variable(next.1.get_index(), source_info), Type::None)),
            (mut parser, TokenType::LSQUARE, _) => {
                consume_list!(parser, ctx, RSQUARE, exprs);
                (parser, Expr::ArrayLiteral(exprs, Type::None))
            }
            (mut parser, TokenType::LPAREN, _) => {
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, RPAREN);
                (parser, Expr::Paren(Box::new(expr)))
            }
            (mut parser, TokenType::IF, _) => {
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, THEN);
                consume!(parser, ctx, Expr, expr2);
                check!(parser, ctx, ELSE);
                consume!(parser, ctx, Expr, expr3);
                (parser, Expr::If(Box::new(expr), Box::new(expr2), Box::new(expr3), Type::None))
            }
            (mut parser, TokenType::ARRAY, _) => {
                check!(parser, ctx, LSQUARE);
                consume_list!(parser, ctx, RSQUARE, fields);
                consume!(parser, ctx, Expr, expr);
                (parser, Expr::ArrayLoop(fields, Box::new(expr), Type::None))
            }
            (mut parser, TokenType::SUM, _) => {
                check!(parser, ctx, LSQUARE);
                consume_list!(parser, ctx, RSQUARE, fields);
                consume!(parser, ctx, Expr, expr);
                (parser, Expr::SumLoop(fields, Box::new(expr), Type::None))
            }
            (_, t, _) => miss!(parser,
                "expected start of expression (INTVAL | FLOATVAL | TRUE | FALSE | VARIABLE | LSQUARE | LPAREN | LCURLY), found {t:?}"
            ),
        };

        let (parser, expr) = loop {
            let (rem_parser, new_expr) = match (parser.next_type(ctx), &expr) {
                ((mut parser, TokenType::LSQUARE), _) => {
                    consume_list!(parser, ctx, RSQUARE, exprs);
                    (parser, Expr::ArrayIndex(Box::new(expr), exprs, Type::None))
                }
                ((mut parser, TokenType::LPAREN), Expr::Variable(s, _)) => {
                    consume_list!(parser, ctx, RPAREN, exprs);
                    (parser, Expr::Call(*s, exprs, Type::None))
                }
                ((mut parser, TokenType::LCURLY), Expr::Variable(s, _)) => {
                    consume_list!(parser, ctx, RCURLY, exprs);
                    (parser, Expr::StructLiteral(*s, exprs, Type::None))
                }
                ((mut parser, TokenType::DOT), _) => {
                    consume!(parser, ctx, Variable, var);
                    (parser, Expr::Dot(Box::new(expr), var, Type::None))
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
                            Expr::Binop(Box::new(new_expr), op, Box::new(right_expr), Type::None)
                        } else {
                            match right_expr {
                                Expr::Binop(mut right_expr_left, c2, right_expr_right, _) => {
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
                                        Type::None,
                                    )
                                }
                                _ => Expr::Binop(
                                    Box::new(new_expr),
                                    op,
                                    Box::new(right_expr),
                                    Type::None,
                                ),
                            }
                        }
                    }

                    consume!(parser, ctx, Expr, expr2);
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

        parser.complete_range(expr, &range)
    }
}

#[derive(Debug, Clone)]
pub enum LValue {
    Var(Variable),
    Array(Variable, Vec<Variable>),
}

impl<'a, 'b> Consume<'a, 'b> for LValue {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("lvalue");
        let next = parser.next(ctx);
        let range = SourceInfo::mark_range(&parser);
        let (parser, lv) = match (next.0, next.1.get_type()) {
            (parser, TokenType::VARIABLE) => {
                (parser, LValue::Var(Variable(next.1.get_index(), next.2)))
            }
            (_, t) => miss!(
                parser,
                "expected start of lvalue (VARIABLE | LCURLY), found {t:?}"
            ),
        };

        let (parser, lv) = match (parser.next_type(ctx), &lv) {
            ((mut parser, TokenType::LSQUARE), &LValue::Var(s)) => {
                consume_list!(parser, ctx, RSQUARE, args);
                (parser, LValue::Array(s, args))
            }
            _ => (parser, lv),
        };

        parser.complete_range(lv, &range)
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    // TODO maybe add wrapping type?
    Struct(Variable),
    Array(Box<Type>, u8),
    Float,
    Int,
    Bool,
    Void,
    None,
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Struct(s), Type::Struct(o)) => s == o,
            (Type::Array(s, l), Type::Array(o, l2)) => s == o && l == l2,
            (Type::Float, Type::Float)
            | (Type::Int, Type::Int)
            | (Type::Bool, Type::Bool)
            | (Type::Void, Type::Void) => true,
            _ => false,
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Type {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("type");
        let range = SourceInfo::mark_range(&parser);

        let next = parser.next(ctx);
        let (mut parser, mut ty) = match (next.0, next.1.get_type()) {
            (parser, TokenType::VARIABLE) => {
                (parser, Type::Struct(Variable(next.1.get_index(), next.2)))
            }
            (parser, TokenType::INT) => (parser, Type::Int),
            (parser, TokenType::BOOL) => (parser, Type::Bool),
            (parser, TokenType::VOID) => (parser, Type::Void),
            (parser, TokenType::FLOAT) => (parser, Type::Float),
            (_, t) => miss!(
                parser,
                "expected start of type (VARIABLE | FLOAT | LCURLY), found {t:?}"
            ),
        };

        while let TokenType::LSQUARE = parser.first_type(ctx) {
            parser = parser.skip_one();

            let mut depth: u8 = 1;

            loop {
                match parser.next_type(ctx) {
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

        parser.complete_range(ty, &range)
    }
}

#[derive(Debug, Clone)]
pub struct Binding(pub LValue, pub Type);

impl<'a, 'b> Consume<'a, 'b> for Binding {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("binding");
        localize_error!(parser, ctx, Binding, {
            let range = SourceInfo::mark_range(&parser);
            consume!(parser, ctx, LValue, lv);
            check!(parser, ctx, COLON);
            consume!(parser, ctx, Type, ty);
            parser.complete_range(Binding(lv, ty), &range)
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
) -> Result<(Vec<Cmd>, Vec<usize>)> {
    measure!("parse");
    let mut cmds = vec![];
    let mut tokens_consumed = vec![];

    let mut parser = Parser {
        current_position: 0,
    };

    let ctx = ParserContext {
        original_tokens: tokens,
        string_map,
        source,
    };

    let ctx = &ctx;

    while !parser.is_empty(ctx) {
        let cmd = Cmd::consume(parser, ctx);

        match cmd {
            ParseResult::Parsed(moved_parser, cmd, _) => {
                parser = moved_parser;

                tokens_consumed.push(parser.current_position);

                let cmd: Cmd = cmd;

                cmds.push(cmd);
            }
            pr => {
                if let TokenType::NEWLINE = parser.first_type(ctx) {
                    parser = parser.skip_one();
                    continue;
                }

                if let TokenType::END_OF_FILE = parser.first_type(ctx) {
                    break;
                }

                let (e, line, column) = match pr {
                    ParseResult::NotParsed {
                        error_message: e,
                        position: err_position,
                    } => {
                        let (line, column) = parser.print_error(ctx, err_position);
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

    debug_assert_eq!(cmds.len(), tokens_consumed.len());

    Ok((cmds, tokens_consumed))
}
