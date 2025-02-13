use ahash::AHashMap;
use anyhow::{bail, ensure, Result};

use crate::{
    lex::TokenType,
    parse::{Binding, Cmd, Expr, Field, LValue, LoopField, Op, Statement, Type, Variable},
    PRINT_TYPES,
};

#[cfg(test)]
mod tests;

#[derive(Debug)]
struct Context {
    structs: AHashMap<usize, Vec<Field>>,
    fns: AHashMap<usize, (Vec<Type>, Type)>,
    vars: AHashMap<usize, Type>,
}

impl Context {
    fn new(string_map: &[&str]) -> Context {
        let mut context = Context {
            structs: AHashMap::new(),
            fns: AHashMap::new(),
            vars: AHashMap::new(),
        };

        debug_assert_eq!(string_map[0], "rgba");
        debug_assert_eq!(string_map[1], "r");
        debug_assert_eq!(string_map[2], "g");
        debug_assert_eq!(string_map[3], "b");
        debug_assert_eq!(string_map[4], "a");
        context.structs.insert(
            0,
            vec![
                Field(Variable(1), Type::Float),
                Field(Variable(2), Type::Float),
                Field(Variable(3), Type::Float),
                Field(Variable(4), Type::Float),
            ],
        );
        debug_assert_eq!(string_map[5], "sqrt");
        context.fns.insert(5, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[6], "exp");
        context.fns.insert(6, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[7], "sin");
        context.fns.insert(7, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[8], "cos");
        context.fns.insert(8, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[9], "tan");
        context.fns.insert(9, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[10], "asin");
        context.fns.insert(10, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[11], "acos");
        context.fns.insert(11, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[12], "atan");
        context.fns.insert(12, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[13], "log");
        context.fns.insert(13, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[14], "pow");
        context
            .fns
            .insert(14, (vec![Type::Float, Type::Float], Type::Float));
        debug_assert_eq!(string_map[15], "atan2");
        context
            .fns
            .insert(15, (vec![Type::Float, Type::Float], Type::Float));
        debug_assert_eq!(string_map[16], "to_float");
        context.fns.insert(16, (vec![Type::Int], Type::Float));
        debug_assert_eq!(string_map[17], "to_int");
        context.fns.insert(17, (vec![Type::Float], Type::Int));
        debug_assert_eq!(string_map[18], "args");
        context.vars.insert(18, Type::Array(Box::new(Type::Int), 1));
        debug_assert_eq!(string_map[19], "argnum");
        context.vars.insert(19, Type::Int);

        context
    }

    fn insert_struct(&mut self, name: usize, data: Vec<Field>, string_map: &[&str]) -> Result<()> {
        if self.vars.contains_key(&name) {
            bail!(
                "cannot define struct {} because variable {} exists",
                string_map[name],
                string_map[name]
            );
        }

        if self.fns.contains_key(&name) {
            bail!(
                "cannot define struct {} because function {} exists",
                string_map[name],
                string_map[name]
            );
        }

        if self.structs.insert(name, data).is_some() {
            bail!("duplicate struct identifier {}", string_map[name]);
        }

        Ok(())
    }

    fn insert_var(&mut self, name: usize, data: Type, string_map: &[&str]) -> Result<()> {
        if self.structs.contains_key(&name) {
            bail!(
                "cannot define variable {} because struct {} exists",
                string_map[name],
                string_map[name]
            );
        }

        if self.fns.contains_key(&name) {
            bail!(
                "cannot define variable {} because function {} exists",
                string_map[name],
                string_map[name]
            );
        }

        if self.vars.insert(name, data).is_some() {
            bail!("duplicate variable identifier {}", string_map[name]);
        }

        Ok(())
    }

    fn insert_fn(
        &mut self,
        name: usize,
        data: (Vec<Type>, Type),
        string_map: &[&str],
    ) -> Result<()> {
        if self.structs.contains_key(&name) {
            bail!(
                "cannot define function {} because struct {} exists",
                string_map[name],
                string_map[name]
            );
        }

        if self.vars.contains_key(&name) {
            bail!(
                "cannot define function {} because variable {} exists",
                string_map[name],
                string_map[name]
            );
        }

        if self.fns.insert(name, data).is_some() {
            bail!("duplicate function identifier {}", string_map[name]);
        }

        Ok(())
    }

    fn validate_type(&self, ty: &Type, string_map: &[&str]) -> Result<()> {
        match ty {
            Type::Struct(ty) => {
                ensure!(
                    self.structs.contains_key(ty),
                    "struct definition references nonexistent struct {}",
                    string_map[*ty]
                );
            }
            Type::Array(ty, _) => self.validate_type(ty, string_map)?,
            _ => {}
        }

        Ok(())
    }
}

trait TypeFill {
    fn typefill(&mut self, context: &mut Context, string_map: &[&str]) -> Result<()>;
}

#[allow(clippy::too_many_lines)]
impl TypeFill for Cmd {
    fn typefill(&mut self, context: &mut Context, string_map: &[&str]) -> Result<()> {
        match self {
            Cmd::Show(expr) => {
                expr.typefill(context, string_map)?;
            }
            Cmd::Struct(Variable(v), fields) => {
                for Field(_, ty) in fields.iter_mut() {
                    context.validate_type(ty, string_map)?;
                }

                context.insert_struct(*v, fields.clone(), string_map)?;
            }
            Cmd::Let(lv, expr) => {
                expr.typefill(context, string_map)?;
                let expr_type = expr.get_type();
                match (lv, &expr_type) {
                    (LValue::Var(Variable(v)), _) => {
                        context.insert_var(*v, expr_type, string_map)?;
                    }
                    (LValue::Array(Variable(v), dim_bindings), Type::Array(_, dims)) => {
                        ensure!(
                            *dims as usize == dim_bindings.len(),
                            "cannot bind array length bindings {:?} to array of dimension {}",
                            dim_bindings,
                            dims
                        );

                        context.insert_var(*v, expr_type, string_map)?;

                        for Variable(bind) in dim_bindings {
                            context.insert_var(*bind, Type::Int, string_map)?;
                        }
                    }
                    (lv, expr_type) => bail!("binding mismatch! {:?} {:?}", lv, expr_type),
                }
            }
            Cmd::Fn(Variable(v), bindings, ty, stmts) => {
                context.insert_fn(
                    *v,
                    (
                        bindings.iter().map(|Binding(_, ty)| ty.clone()).collect(),
                        ty.clone(),
                    ),
                    string_map,
                )?;

                let mut let_cleanup = vec![];

                for Binding(lv, ty) in bindings.iter() {
                    match lv {
                        LValue::Var(Variable(v)) => {
                            let_cleanup.push(*v);
                            context.insert_var(*v, ty.clone(), string_map)?;
                        }
                        LValue::Array(Variable(v), dim_bindings) => {
                            let_cleanup.push(*v);
                            context.insert_var(*v, ty.clone(), string_map)?;

                            for Variable(bind) in dim_bindings {
                                let_cleanup.push(*bind);
                                context.insert_var(*bind, Type::Int, string_map)?;
                            }
                        }
                    }
                }

                let mut has_return = false;

                for stmt in stmts {
                    match stmt {
                        Statement::Return(expr) => {
                            has_return = true;
                            expr.typefill(context, string_map)?;
                            let expr_type = expr.get_type();
                            ensure!(
                                expr_type == *ty,
                                "return statment expected to return {:?}, returns {:?}",
                                ty,
                                expr_type
                            );
                        }
                        Statement::Assert(expr, _) => {
                            expr.typefill(context, string_map)?;
                            let expr_type = expr.get_type();
                            ensure!(
                                expr_type == Type::Bool,
                                "assert statement requires a bool, got {:?}",
                                expr_type
                            );
                        }
                        Statement::Let(lv, expr) => {
                            expr.typefill(context, string_map)?;
                            let expr_type = expr.get_type();
                            match (lv, &expr_type) {
                                (LValue::Var(Variable(v)), _) => {
                                    context.insert_var(*v, expr_type, string_map)?;
                                    let_cleanup.push(*v);
                                }
                                (
                                    LValue::Array(Variable(v), dim_bindings),
                                    Type::Array(_, dims),
                                ) => {
                                    ensure!(
                                        *dims as usize == dim_bindings.len(),
                                        "Cannot bind array length bindings {:?} to array of dimension {}",
                                        dim_bindings,
                                        dims
                                    );

                                    context.insert_var(*v, expr_type, string_map)?;
                                    let_cleanup.push(*v);

                                    for Variable(bind) in dim_bindings {
                                        context.insert_var(*bind, Type::Int, string_map)?;
                                        let_cleanup.push(*bind);
                                    }
                                }
                                lv => {
                                    bail!("incompatible bindings {:?} for type {:?}", lv, expr_type)
                                }
                            }
                        }
                    }
                }

                if !has_return && *ty != Type::Void {
                    bail!(
                        "function claims to return a value of type {:?} but never does",
                        ty
                    );
                }

                for v in let_cleanup {
                    context.vars.remove(&v);
                }
            }
            Cmd::Write(expr, _) => {
                expr.typefill(context, string_map)?;
                let expr_type = expr.get_type();
                if expr_type != Type::Array(Box::new(Type::Struct(0)), 2) {
                    bail!("write takes rgba[,], found {:?}", expr_type)
                }
            }
            Cmd::Read(_, lv) => {
                let dims = 2;
                let expr_type = Type::Array(Box::new(Type::Struct(0)), 2);
                match lv {
                    LValue::Var(Variable(v)) => context.insert_var(*v, expr_type, string_map)?,
                    LValue::Array(Variable(v), dim_bindings) => {
                        ensure!(
                            dims == dim_bindings.len(),
                            "Cannot bind array length bindings {:?} to array of dimension {}",
                            dim_bindings,
                            dims
                        );

                        context.insert_var(*v, expr_type, string_map)?;

                        for Variable(bind) in dim_bindings {
                            context.insert_var(*bind, Type::Int, string_map)?;
                        }
                    }
                }
            }
            Cmd::Time(cmd) => {
                cmd.typefill(context, string_map)?;
            }
            Cmd::Assert(expr, _) => {
                expr.typefill(context, string_map)?;
                let expr_type = expr.get_type();
                ensure!(
                    expr_type == Type::Bool,
                    "assert command requires a bool, got {:?}",
                    expr_type
                );
            }
            Cmd::Print(_) => {}
        };

        Ok(())
    }
}

/// # Errors
#[allow(clippy::too_many_lines)]
pub fn typecheck(cmds: &mut [Cmd], string_map: &[&str]) -> Result<()> {
    let mut context = Context::new(string_map);

    for cmd in cmds {
        cmd.typefill(&mut context, string_map)?;
    }

    PRINT_TYPES.with(|print_types| print_types.set(true));

    Ok(())
}

#[allow(clippy::too_many_lines)]
impl TypeFill for Expr {
    fn typefill(&mut self, context: &mut Context, string_map: &[&str]) -> Result<()> {
        match self {
            Expr::Int(_, _) | Expr::Float(_, _) | Expr::True | Expr::False | Expr::Void => {}
            Expr::Binop(lhs, op, rhs, ret_ty) => {
                lhs.typefill(context, string_map)?;
                rhs.typefill(context, string_map)?;
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
                expr.typefill(context, string_map)?;
                let expr_type = expr.get_type();
                *ret_ty = match (&op, &expr_type) {
                    (Op(TokenType::Not), Type::Bool)
                    | (Op(TokenType::Sub), Type::Int | Type::Float) => expr_type,
                    _ => bail!("Cannot perform unary operation {:?} {:?}", op, expr_type),
                }
            }
            Expr::Paren(expr) => {
                expr.typefill(context, string_map)?;
            }
            Expr::ArrayIndex(array, indexes, ret_ty) => {
                array.typefill(context, string_map)?;
                let array = array.get_type();
                match array {
                    Type::Array(ty, dims) => {
                        ensure!(
                            indexes.len() as u8 == dims,
                            "Cannot index {} dimensional array with {} indices",
                            dims,
                            indexes.len()
                        );

                        *ret_ty = *ty;
                    }
                    ty => bail!("cannot array index non array, found {:#?}", ty),
                }

                for index in indexes {
                    index.typefill(context, string_map)?;
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
                    expr.typefill(context, string_map)?;
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

                *ty = Type::Array(
                    Box::new(ty.clone()),
                    // TODO ?
                    //Type::Array(_, d) => *d + 1,
                    1,
                );
            }
            Expr::StructLiteral(Variable(v), exprs, ty) => {
                for expr in exprs.iter_mut() {
                    expr.typefill(context, string_map)?;
                }

                let Some(struct_type) = context.structs.get(v) else {
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
                expr.typefill(context, string_map)?;
                let struct_type = match expr.get_type() {
                    Type::Struct(struct_type) => struct_type,
                    t => bail!("Cannot perform operation `.` on non struct {:?}", t),
                };

                let Some(fields) = context.structs.get(&struct_type) else {
                    bail!("Struct of type {} is not defined", string_map[*v]);
                };

                let Some(Field(_, fty)) = fields.iter().find(|Field(Variable(fv), _)| fv == v)
                else {
                    bail!(
                        "Field {} does not exist on struct of type {}",
                        string_map[*v],
                        string_map[struct_type]
                    );
                };

                *ty = fty.clone();
            }
            Expr::Call(Variable(v), exprs, ty) => {
                for expr in exprs.iter_mut() {
                    expr.typefill(context, string_map)?;
                }

                let Some((args, ret_type)) = context.fns.get(v) else {
                    bail!("struct of type {} is not defined", string_map[*v]);
                };

                match exprs.len().cmp(&args.len()) {
                    std::cmp::Ordering::Less => {
                        bail!("too few arguments passed to function {}", string_map[*v])
                    }
                    std::cmp::Ordering::Greater => {
                        bail!("too many arguments passed to function {}", string_map[*v])
                    }
                    std::cmp::Ordering::Equal => {}
                }

                for (expr_type, arg_type) in exprs.iter().map(Expr::get_type).zip(args.iter()) {
                    ensure!(
                        expr_type == *arg_type,
                        "function argument is of type {:?}, received {:?}",
                        arg_type,
                        expr_type
                    );
                }

                *ty = ret_type.clone();
            }
            Expr::If(cond, r#true, r#false, ty) => {
                cond.typefill(context, string_map)?;
                let cond_type = cond.get_type();
                ensure!(
                    matches!(cond_type, Type::Bool),
                    "Condition in if expression must be a boolean, found {:?}",
                    cond_type
                );
                r#true.typefill(context, string_map)?;
                let true_type = r#true.get_type();
                r#false.typefill(context, string_map)?;
                let false_type = r#false.get_type();

                ensure!(
                    true_type == false_type,
                    "Both branches of an if expression must match types. Found {:?} and {:?}",
                    true_type,
                    false_type
                );

                *ty = true_type;
            }
            Expr::Variable(Variable(v), ret_ty) => {
                let Some(ty) = context.vars.get(v) else {
                    bail!("Variable {} is undefined", string_map[*v]);
                };

                *ret_ty = ty.clone();
            }
            Expr::ArrayLoop(fields, expr, ret_ty) => {
                ensure!(!fields.is_empty(), "loops require at least one field");

                for LoopField(_, le) in fields.iter_mut() {
                    le.typefill(context, string_map)?;
                    ensure!(
                        le.get_type() == Type::Int,
                        "can only loop over integers, found {:?}",
                        le.get_type()
                    );
                }

                for LoopField(Variable(lv), le) in fields.iter_mut() {
                    context.insert_var(*lv, le.get_type(), string_map)?;
                }

                expr.typefill(context, string_map)?;
                *ret_ty = Type::Array(Box::new(expr.get_type()), fields.len() as u8);

                for LoopField(Variable(lv), _) in fields {
                    context.vars.remove(lv);
                }
            }
            Expr::SumLoop(fields, expr, ret_ty) => {
                ensure!(!fields.is_empty(), "loops require at least one field");

                for LoopField(_, le) in fields.iter_mut() {
                    le.typefill(context, string_map)?;
                    ensure!(
                        le.get_type() == Type::Int,
                        "can only loop over integers, found {:?}",
                        le.get_type()
                    );
                }

                for LoopField(Variable(lv), le) in fields.iter_mut() {
                    context.insert_var(*lv, le.get_type(), string_map)?;
                }

                expr.typefill(context, string_map)?;
                *ret_ty = expr.get_type();

                ensure!(
                    matches!(ret_ty, Type::Int | Type::Float),
                    "you can only sum to an integer or float, found {:?}",
                    ret_ty
                );

                for LoopField(Variable(lv), _) in fields {
                    context.vars.remove(lv);
                }
            }
        }

        Ok(())
    }
}
