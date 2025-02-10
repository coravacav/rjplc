use ahash::AHashMap;
use anyhow::{bail, ensure, Result};

use crate::{
    lex::TokenType,
    parse::{Cmd, Expr, Field, Op, Type, Variable},
    PRINT_TYPES,
};

#[cfg(test)]
mod tests;

#[derive(Debug)]
struct Context {
    named_types: AHashMap<usize, Vec<Field>>,
}

/// # Errors
pub fn typecheck(cmds: &mut [Cmd], string_map: &[&str]) -> Result<()> {
    let mut context = Context {
        named_types: AHashMap::new(),
    };

    debug_assert_eq!(string_map[0], "rgba");
    debug_assert_eq!(string_map[1], "r");
    debug_assert_eq!(string_map[2], "g");
    debug_assert_eq!(string_map[3], "b");
    debug_assert_eq!(string_map[4], "a");
    context.named_types.insert(
        0,
        vec![
            Field(Variable(1), Type::Float),
            Field(Variable(2), Type::Float),
            Field(Variable(3), Type::Float),
            Field(Variable(4), Type::Float),
        ],
    );

    for cmd in cmds {
        match cmd {
            Cmd::Show(expr) => {
                typefill_expr(expr, &mut context, string_map)?;
            }
            Cmd::Struct(Variable(v), fields) => {
                if context.named_types.insert(*v, fields.clone()).is_some() {
                    bail!("Struct {} defined more than once", string_map[*v])
                }
            }
            _ => todo!("{cmd:?}"),
        }
    }

    PRINT_TYPES.with(|print_types| print_types.set(true));

    Ok(())
}

#[allow(clippy::too_many_lines)]
fn typefill_expr(expr: &mut Expr, context: &mut Context, string_map: &[&str]) -> Result<()> {
    match expr {
        Expr::Int(_, _) | Expr::Float(_, _) | Expr::True | Expr::False | Expr::Void => {}
        Expr::Binop(lhs, op, rhs, ret_ty) => {
            typefill_expr(lhs, context, string_map)?;
            typefill_expr(rhs, context, string_map)?;
            let lhs_type = lhs.get_type();
            let rhs_type = rhs.get_type();
            *ret_ty = match (&lhs_type, &op, &rhs_type) {
                (
                    Type::Int | Type::Float,
                    Op(
                        TokenType::Eq
                        | TokenType::LessEq
                        | TokenType::Greater
                        | TokenType::Less
                        | TokenType::GreaterEq
                        | TokenType::Neq,
                    ),
                    Type::Int | Type::Float,
                ) if lhs_type == rhs_type => Type::Bool,
                (
                    Type::Bool,
                    Op(TokenType::Eq | TokenType::Neq | TokenType::Or | TokenType::And),
                    Type::Bool,
                ) => Type::Bool,
                (
                    Type::Int | Type::Float,
                    Op(
                        TokenType::Sub
                        | TokenType::Mod
                        | TokenType::Add
                        | TokenType::Div
                        | TokenType::Mul,
                    ),
                    Type::Int | Type::Float,
                ) if lhs_type == rhs_type => lhs_type,
                _ => bail!(
                    "Cannot perform binary operation {:?} {:?} {:?}",
                    lhs_type,
                    op,
                    rhs_type
                ),
            }
        }
        Expr::Unop(op, expr, ret_ty) => {
            typefill_expr(expr, context, string_map)?;
            let expr_type = expr.get_type();
            *ret_ty = match (&op, &expr_type) {
                (Op(TokenType::Not), Type::Bool)
                | (Op(TokenType::Sub), Type::Int | Type::Float) => expr_type,
                _ => bail!("Cannot perform unary operation {:?} {:?}", op, expr_type),
            }
        }
        Expr::Paren(expr) => {
            typefill_expr(expr, context, string_map)?;
        }
        Expr::ArrayIndex(array, indexes, ret_ty) => {
            typefill_expr(array, context, string_map)?;
            let array = array.get_type();
            match array {
                Type::Array(ty, _) => {
                    *ret_ty = *ty;
                }
                ty => bail!("cannot array index non array, found {:#?}", ty),
            }

            for index in indexes {
                typefill_expr(index, context, string_map)?;
                let index = index.get_type();
                ensure!(
                    matches!(index, Type::Int),
                    "indexing an array must be done with an integer, got {:#?}",
                    index
                );
            }
        }
        Expr::ArrayLiteral(exprs, ref mut ty) => {
            for expr in exprs.iter_mut() {
                typefill_expr(expr, context, string_map)?;
                let expr = expr.get_type();
                if matches!(ty, Type::None) {
                    *ty = expr;
                } else {
                    ensure!(
                        expr == *ty,
                        "array literal must be all of equal type, expected {:#?}, got {:#?}",
                        ty,
                        expr
                    );
                }
            }

            dbg!(&ty);

            *ty = Type::Array(
                Box::new(ty.clone()),
                match ty {
                    // TODO ?
                    //Type::Array(_, d) => *d + 1,
                    _ => 1,
                },
            );
        }
        Expr::StructLiteral(Variable(v), exprs, ty) => {
            for expr in exprs.iter_mut() {
                typefill_expr(expr, context, string_map)?;
            }

            let Some(struct_type) = context.named_types.get(v) else {
                bail!("Struct of type {} is not defined", string_map[*v])
            };

            *ty = Type::Struct(*v);

            for (expr_type, Field(Variable(fv), field_type)) in
                exprs.iter().map(Expr::get_type).zip(struct_type.iter())
            {
                ensure!(
                    expr_type == *field_type,
                    "Struct field {} is of type {:?}, received {:?}",
                    string_map[*fv],
                    field_type,
                    expr_type
                );
            }
        }
        Expr::Dot(expr, Variable(v), ty) => {
            typefill_expr(expr, context, string_map)?;
            let struct_type = match expr.get_type() {
                Type::Struct(struct_type) => struct_type,
                t => bail!("Cannot perform operation `.` on non struct {:?}", t),
            };

            let Some(fields) = context.named_types.get(&struct_type) else {
                bail!("Struct of type {} is not defined", string_map[*v]);
            };

            let Some(Field(_, fty)) = fields.iter().find(|Field(Variable(fv), _)| fv == v) else {
                bail!(
                    "Field {} does not exist on struct of type {}",
                    string_map[*v],
                    string_map[struct_type]
                );
            };

            *ty = fty.clone();
        }
        Expr::If(cond, r#true, r#false, ty) => {
            typefill_expr(cond, context, string_map)?;
            let cond_type = cond.get_type();
            ensure!(
                matches!(cond_type, Type::Bool),
                "Condition in if expression must be a boolean, found {:?}",
                cond_type
            );
            typefill_expr(r#true, context, string_map)?;
            let true_type = r#true.get_type();
            typefill_expr(r#false, context, string_map)?;
            let false_type = r#false.get_type();

            ensure!(
                true_type == false_type,
                "Both branches of an if expression must match types. Found {:?} and {:?}",
                true_type,
                false_type
            );

            *ty = true_type;
        }
        _ => todo!("{expr:#?}"),
    }

    Ok(())
}
