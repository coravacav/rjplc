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

pub use parser::Span;

mod parser;
mod printing;
#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy)]
pub struct Variable(pub usize, pub Span);

impl<'a, 'b> Consume<'a, 'b> for Variable {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("variable");
        let (parser, s, span) = match parser.next(ctx) {
            (parser, t, span) if t.get_type() == TokenType::VARIABLE => {
                (parser, t.get_index(), span)
            }
            (_, t, _) => miss!(parser, "expected variable, found {:?}", t),
        };

        parser.complete(Self(s, span))
    }
}

impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LiteralString(usize, Span);

impl<'a, 'b> Consume<'a, 'b> for LiteralString {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("string_lit");
        let (s, span) = match parser.first(ctx) {
            (t, span) if t.get_type() == TokenType::STRING => (t.get_index(), span),
            t => miss!(parser, "expected string, found {t:?}"),
        };

        parser.skip_one().complete(Self(s, span))
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
            consume!(parser, ctx, Variable, s);
            check!(parser, ctx, COLON);
            consume!(parser, ctx, Expr, expr);

            parser.complete(LoopField(s, expr))
        })
    }
}

#[derive(Debug, Clone)]
pub struct Field(pub Variable, pub Type);

impl<'a, 'b> Consume<'a, 'b> for Field {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("field");
        localize_error!(parser, ctx, Field, {
            consume!(parser, ctx, Variable, s);
            check!(parser, ctx, COLON);
            consume!(parser, ctx, Type, ty);
            parser.complete(Field(s, ty))
        })
    }
}

#[derive(Debug, Clone)]
pub enum CommandKind {
    Read(LiteralString, LValue),
    Write(Expr, LiteralString),
    Let(LValue, Expr),
    Assert(Expr, LiteralString),
    Print(LiteralString),
    Show(Expr),
    Time(Box<Command>),
    Fn(Variable, Vec<Binding>, Type, Vec<Statement>),
    Struct(Variable, Vec<Field>),
}

impl CommandKind {
    #[must_use]
    #[allow(clippy::wrong_self_convention)]
    fn to_cmd(self, span: Span) -> Command {
        Command { kind: self, span }
    }
}

#[derive(Debug, Clone)]
pub struct Command {
    pub kind: CommandKind,
    pub span: Span,
}

impl From<Command> for CommandKind {
    fn from(val: Command) -> Self {
        val.kind
    }
}

impl<'a, 'b> Consume<'a, 'b> for Command {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("cmd");
        let start = Span::mark_range(&parser);
        let (parser, cmd) = match parser.next_type(ctx) {
            (mut parser, TokenType::READ)=> {
                check!(parser, ctx, IMAGE);
                consume!(parser, ctx, LiteralString, s);
                check!(parser, ctx, TO);
                consume!(parser, ctx, LValue, lvalue);
                check!(parser, ctx, NEWLINE);
                (parser, CommandKind::Read(s, lvalue))
            }
            (mut parser, TokenType::TIME)=> {
                consume!(parser, ctx, Command, cmd);
                (parser, CommandKind::Time(Box::new(cmd)))
            }
            (mut parser, TokenType::LET)=> {
                consume!(parser, ctx, LValue, lvalue);
                check!(parser, ctx, EQUALS);
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, NEWLINE);
                (parser, CommandKind::Let(lvalue, expr))
            }
            (mut parser, TokenType::ASSERT)=> {
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, COMMA);
                consume!(parser, ctx, LiteralString, s);
                check!(parser, ctx, NEWLINE);
                (parser, CommandKind::Assert(expr, s))
            }
            (mut parser, TokenType::SHOW)=> {
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, NEWLINE);
                (parser, CommandKind::Show(expr))
            }
            (mut parser, TokenType::WRITE)=> {
                check!(parser, ctx, IMAGE);
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, TO);
                consume!(parser, ctx, LiteralString, s);
                check!(parser, ctx, NEWLINE);
                (parser, CommandKind::Write(expr, s))
            }
            (mut parser, TokenType::PRINT)=> {
                consume!(parser, ctx, LiteralString, s);
                check!(parser, ctx, NEWLINE);
                (parser, CommandKind::Print(s))
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
                (parser, CommandKind::Fn(v, bindings, ty, statements))
            }
            (mut parser, TokenType::STRUCT)=> {
                consume!(parser, ctx, Variable, v);
                check!(parser, ctx, LCURLY);
                check!(parser, ctx, NEWLINE);
                consume_list!(parser, ctx, RCURLY, NEWLINE, fields);
                (parser, CommandKind::Struct(v, fields))
            }
            (_, t)=> miss!(parser, "expected a command keyword (ASSERT | RETURN | LET | ASSERT | PRINT | SHOW | TIME | FN | TYPE | STRUCT), found {t:?}"),
        };

        let end = Span::mark_range(&parser);
        parser.complete(cmd.to_cmd(start.finish(end)))
    }
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    Let(LValue, Expr),
    Assert(Expr, LiteralString),
    Return(Expr),
}


impl StatementKind {
    #[allow(clippy::wrong_self_convention)]
    fn to_stmt(self, span: Span) -> Statement {
        Statement { kind: self, span }
    }
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

impl From<Statement> for StatementKind {
    fn from(val: Statement) -> Self {
        val.kind
    }
}


impl<'a, 'b> Consume<'a, 'b> for Statement {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("statement");

        localize_error!(parser, ctx, Statement, {
            let start = Span::mark_range(&parser);
            let statement = match parser.first_type(ctx) {
                TokenType::ASSERT => {
                    parser = parser.skip_one();
                    consume!(parser, ctx, Expr, expr);
                    check!(parser, ctx, COMMA);
                    consume!(parser, ctx, LiteralString, msg);
                    StatementKind::Assert(expr, msg)
                }
                TokenType::RETURN => {
                    parser = parser.skip_one();
                    consume!(parser, ctx, Expr, expr);
                    StatementKind::Return(expr)
                }
                TokenType::LET => {
                    parser = parser.skip_one();
                    consume!(parser, ctx, LValue, lvalue);
                    check!(parser, ctx, EQUALS);
                    consume!(parser, ctx, Expr, expr);
                    StatementKind::Let(lvalue, expr)
                }
                t => miss!(
                    parser,
                    "expected a start of statement (ASSERT | RETURN | LET), found {t:?}"
                ),
            };

            let end = Span::mark_range(&parser);

            parser.complete(statement.to_stmt(start.finish(end)))
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
pub enum ExprKind {
    Int(i64, usize),
    Float(f64, usize),
    True,
    False,
    Void,
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

impl ExprKind {
    #[allow(clippy::wrong_self_convention)]
    fn to_expr(self, span: Span) -> Expr {
        Expr { kind: self, span }
    }
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl From<Expr> for ExprKind {
    fn from(val: Expr) -> Self {
        val.kind
    }
}

impl Expr {
    const UNOP_PRECEDENCE: u8 = 6;

    const fn precedence(&self) -> u8 {
        match self.kind {
            ExprKind::ArrayIndex(_, _, _) => 7,
            ExprKind::Unop(_, _, _) => Self::UNOP_PRECEDENCE,
            ExprKind::Binop(_, op, _, _) => op.precedence(),
            ExprKind::If(_, _, _, _)
            | ExprKind::ArrayLoop(_, _, _)
            | ExprKind::SumLoop(_, _, _) => 1,
            _ => u8::MAX,
        }
    }

    #[must_use]
    pub fn get_type(&self) -> Type {
        match &self.kind {
            ExprKind::Int(_, _) => TypeKind::Int.to_type(self.span),
            ExprKind::Float(_, _) => TypeKind::Float.to_type(self.span),
            ExprKind::Void => TypeKind::Void.to_type(self.span),
            ExprKind::True | ExprKind::False => TypeKind::Bool.to_type(self.span),
            ExprKind::Paren(expr) => expr.get_type(),
            ExprKind::ArrayLiteral(_, ty)
            | ExprKind::StructLiteral(_, _, ty)
            | ExprKind::ArrayLoop(_, _, ty)
            | ExprKind::SumLoop(_, _, ty)
            | ExprKind::Dot(_, _, ty)
            | ExprKind::Binop(_, _, _, ty)
            | ExprKind::Unop(_, _, ty)
            | ExprKind::Variable(_, ty)
            | ExprKind::Call(_, _, ty)
            | ExprKind::If(_, _, _, ty)
            | ExprKind::ArrayIndex(_, _, ty) => ty.kind.clone().to_type(self.span),
        }
    }
}

impl<'a, 'b> Consume<'a, 'b> for Expr {
    #[allow(clippy::too_many_lines)]
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("expr");
        let next = parser.next(ctx);
        let start = Span::mark_range(&parser);
        let (mut parser, mut expr) = match (next.0, next.1.get_type(), next.2) {
            (mut parser, op @ (TokenType::Not | TokenType::Sub), _) => {
                measure!("unop");
                fn rearrange_according_to_precedence(
                    op: Op,
                    right_expr: Expr,
                ) -> Expr {
                    if Expr::UNOP_PRECEDENCE < right_expr.precedence() {
                        let expr_span = right_expr.span;
                        ExprKind::Unop(op, Box::new(right_expr), Type::NONE).to_expr(expr_span.extend_back(1))
                    } else if let ExprKind::Binop(mut right_expr_left, c2, right_expr_right, _) = right_expr.kind {
                            let left_expr_span = right_expr_left.span;
                            let right_expr_span = right_expr_right.span;

                            ExprKind::Binop(
                            {
                                // reuse the allocation from right_expr_left 
                                *right_expr_left = rearrange_according_to_precedence(op, *right_expr_left);
                                right_expr_left
                            },
                            c2,
                            right_expr_right,
                            Type::NONE,
                        ).to_expr(Span::Range(
                            left_expr_span.start(),
                            right_expr_span.end(),
                        ))
                    
                    } else {
                        let expr_span = right_expr.span;
                        ExprKind::Unop(op, Box::new(right_expr), Type::NONE).to_expr(expr_span.extend_back(1))
                    }
                }

                consume!(parser, ctx, Expr, expr);
                (parser, rearrange_according_to_precedence(op.into(), expr))
            }
            (parser, TokenType::INTVAL, span) => {
                let si = next.1.get_index();
                let s = ctx.string_map[si];
                if let Ok(i) = s.parse::<i64>() {
                    (parser, ExprKind::Int(i, si).to_expr(span))
                } else {
                    miss!(parser, "couldn't parse integer {s}")
                }
            }
            (parser, TokenType::FLOATVAL, span) => {
                let si = next.1.get_index();
                let s = ctx.string_map[si];
                if let Ok(f) = s.parse::<f64>() {
                    if !f.is_finite() {
                        miss!(parser, "expected a finite float, found {f}");
                    }

                    (parser, ExprKind::Float(f, si).to_expr(span))
                } else {
                    miss!(parser, "couldn't parse float {s}")
                }
            }
            (parser, TokenType::VOID, span) => (parser, ExprKind::Void.to_expr(span)),
            (parser, TokenType::TRUE, span) => (parser, ExprKind::True.to_expr(span)),
            (parser, TokenType::FALSE, span) => (parser, ExprKind::False.to_expr(span)),
            (parser, TokenType::VARIABLE, span) => (parser, ExprKind::Variable(Variable(next.1.get_index(), span), Type::NONE).to_expr(span)),
            (mut parser, TokenType::LSQUARE, _) => {
                consume_list!(parser, ctx, RSQUARE, exprs);
                let end = Span::mark_range(&parser);
                (parser, ExprKind::ArrayLiteral(exprs, Type::NONE).to_expr(start.finish(end)))
            }
            (mut parser, TokenType::LPAREN, _) => {
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, RPAREN);
                let end = Span::mark_range(&parser);
                (parser, ExprKind::Paren(Box::new(expr)).to_expr(start.finish(end)))
            }
            (mut parser, TokenType::IF, _) => {
                consume!(parser, ctx, Expr, expr);
                check!(parser, ctx, THEN);
                consume!(parser, ctx, Expr, expr2);
                check!(parser, ctx, ELSE);
                consume!(parser, ctx, Expr, expr3);
                let end = Span::mark_range(&parser);
                (parser, ExprKind::If(Box::new(expr), Box::new(expr2), Box::new(expr3), Type::NONE).to_expr(start.finish(end)))
            }
            (mut parser, TokenType::ARRAY, _) => {
                check!(parser, ctx, LSQUARE);
                consume_list!(parser, ctx, RSQUARE, fields);
                consume!(parser, ctx, Expr, expr);
                let end = Span::mark_range(&parser);
                (parser, ExprKind::ArrayLoop(fields, Box::new(expr), Type::NONE).to_expr(start.finish(end)))
            }
            (mut parser, TokenType::SUM, _) => {
                check!(parser, ctx, LSQUARE);
                consume_list!(parser, ctx, RSQUARE, fields);
                consume!(parser, ctx, Expr, expr);
                let end = Span::mark_range(&parser);
                (parser, ExprKind::SumLoop(fields, Box::new(expr), Type::NONE).to_expr(start.finish(end)))
            }
            (_, t, _) => miss!(parser,
                "expected start of expression (INTVAL | FLOATVAL | TRUE | FALSE | VARIABLE | LSQUARE | LPAREN | LCURLY), found {t:?}"
            ),
        };

        let (parser, expr) = loop {
            let start = Span::mark_range(&parser);
            let (rem_parser, new_expr) = match (parser.next_type(ctx), &expr.kind) {
                ((mut parser, TokenType::LSQUARE), _) => {
                    consume_list!(parser, ctx, RSQUARE, exprs);
                    let end = Span::mark_range(&parser);
                    (
                        parser,
                        ExprKind::ArrayIndex(Box::new(expr), exprs, Type::NONE)
                            .to_expr(start.finish(end)),
                    )
                }
                ((mut parser, TokenType::LPAREN), ExprKind::Variable(s, _)) => {
                    consume_list!(parser, ctx, RPAREN, exprs);
                    let end = Span::mark_range(&parser);
                    (
                        parser,
                        ExprKind::Call(*s, exprs, Type::NONE).to_expr(start.finish(end)),
                    )
                }
                ((mut parser, TokenType::LCURLY), ExprKind::Variable(s, _)) => {
                    consume_list!(parser, ctx, RCURLY, exprs);
                    let end = Span::mark_range(&parser);
                    (
                        parser,
                        ExprKind::StructLiteral(*s, exprs, Type::NONE).to_expr(start.finish(end)),
                    )
                }
                ((mut parser, TokenType::DOT), _) => {
                    consume!(parser, ctx, Variable, var);
                    let end = Span::mark_range(&parser);
                    (
                        parser,
                        ExprKind::Dot(Box::new(expr), var, Type::NONE).to_expr(start.finish(end)),
                    )
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
                            let left_expr_span = new_expr.span;
                            let right_expr_span = right_expr.span;

                            ExprKind::Binop(
                                Box::new(new_expr),
                                op,
                                Box::new(right_expr),
                                Type::NONE,
                            )
                            .to_expr(Span::Range(left_expr_span.start(), right_expr_span.end()))
                        } else if let ExprKind::Binop(mut right_expr_left, c2, right_expr_right, _) = right_expr.kind {
                            let left_expr = {
                                // reuxe the allocation from right_expr_left
                                *right_expr_left = rearrange_according_to_precedence(
                                    new_expr,
                                    op,
                                    *right_expr_left,
                                );
                                right_expr_left
                            };

                            let left_expr_span = left_expr.span;
                            let right_expr_span = right_expr_right.span;

                            ExprKind::Binop(left_expr, c2, right_expr_right, Type::NONE)
                                .to_expr(Span::Range(
                                    left_expr_span.start(),
                                    right_expr_span.end(),
                                ))
                        } else {
                            let left_expr_span = new_expr.span;
                            let right_expr_span = right_expr.span;

                            ExprKind::Binop(
                                Box::new(new_expr),
                                op,
                                Box::new(right_expr),
                                Type::NONE,
                            )
                            .to_expr(Span::Range(
                                left_expr_span.start(),
                                right_expr_span.end(),
                            ))
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

        parser.complete(expr)
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

        parser.complete(lv)
    }
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    Struct(Variable),
    Array(Box<Type>, u8),
    Float,
    Int,
    Bool,
    Void,
    None,
}

impl PartialEq for TypeKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TypeKind::Struct(s), TypeKind::Struct(o)) => s == o,
            (TypeKind::Array(s, l), TypeKind::Array(o, l2)) => s.kind == o.kind && l == l2,
            (TypeKind::Float, TypeKind::Float)
            | (TypeKind::Int, TypeKind::Int)
            | (TypeKind::Bool, TypeKind::Bool)
            | (TypeKind::Void, TypeKind::Void) => true,
            _ => false,
        }
    }
}

impl TypeKind {
    #[must_use] 
    pub fn to_type(self, span: Span) -> Type { 
        Type { kind: self, span }
    }
}

#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

impl Type {
    const NONE: Type = Type {
        kind: TypeKind::None,
        span: Span::Builtin,
    };
}

impl From<Type> for TypeKind {
    fn from(val: Type) -> Self {
        val.kind
    }
}

impl<'a, 'b> Consume<'a, 'b> for Type {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("type");
        let start = Span::mark_range(&parser);

        let (mut parser, tt, span) = parser.next(ctx);
        let mut ty = match tt.get_type() {
            TokenType::VARIABLE => {
                TypeKind::Struct(Variable(tt.get_index(), span)).to_type(span)
            }
            TokenType::INT => TypeKind::Int.to_type(span),
            TokenType::BOOL => TypeKind::Bool.to_type(span),
            TokenType::VOID => TypeKind::Void.to_type(span),
            TokenType::FLOAT => TypeKind::Float.to_type(span),
            t => miss!(
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

            ty = TypeKind::Array(Box::new(ty), depth).to_type(start.finish(Span::mark_range(&parser)));
        }

        parser.complete(ty)
    }
}

#[derive(Debug, Clone)]
pub struct Binding(pub LValue, pub Type);

impl<'a, 'b> Consume<'a, 'b> for Binding {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self> {
        measure!("binding");
        localize_error!(parser, ctx, Binding, {
            consume!(parser, ctx, LValue, lv);
            check!(parser, ctx, COLON);
            consume!(parser, ctx, Type, ty);
            parser.complete(Binding(lv, ty))
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
) -> Result<(Vec<Command>, Vec<usize>)> {
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
        let cmd = Command::consume(parser, ctx);

        match cmd {
            ParseResult::Parsed(moved_parser, cmd) => {
                parser = moved_parser;

                tokens_consumed.push(parser.current_position);

                let cmd: Command = cmd;

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
