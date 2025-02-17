use std::cmp::Ordering;

use ahash::AHashMap;
use anyhow::{anyhow, bail, ensure, Context, Result};

use crate::{
    lex::TokenType,
    parse::{Binding, Cmd, Expr, Field, LValue, LoopField, Op, Statement, Type, Variable},
    PRINT_TYPES,
};

#[cfg(test)]
mod tests;

#[derive(Debug)]
struct Ctx<'a, 'b> {
    structs: AHashMap<usize, Vec<Field>>,
    fns: AHashMap<usize, (Vec<Type>, Type)>,
    vars: AHashMap<usize, Type>,
    temporary_vars: AHashMap<usize, Type>,
    string_map: &'b [&'a str],
}

impl<'a, 'b> Ctx<'a, 'b> {
    fn new(string_map: &'b [&'a str]) -> Ctx<'a, 'b> {
        let mut ctx = Ctx {
            structs: AHashMap::new(),
            fns: AHashMap::new(),
            vars: AHashMap::new(),
            temporary_vars: AHashMap::new(),
            string_map,
        };

        debug_assert_eq!(string_map[0], "rgba");
        debug_assert_eq!(string_map[1], "r");
        debug_assert_eq!(string_map[2], "g");
        debug_assert_eq!(string_map[3], "b");
        debug_assert_eq!(string_map[4], "a");
        ctx.structs.insert(
            0,
            vec![
                Field(Variable(1), Type::Float),
                Field(Variable(2), Type::Float),
                Field(Variable(3), Type::Float),
                Field(Variable(4), Type::Float),
            ],
        );
        debug_assert_eq!(string_map[5], "sqrt");
        ctx.fns.insert(5, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[6], "exp");
        ctx.fns.insert(6, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[7], "sin");
        ctx.fns.insert(7, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[8], "cos");
        ctx.fns.insert(8, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[9], "tan");
        ctx.fns.insert(9, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[10], "asin");
        ctx.fns.insert(10, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[11], "acos");
        ctx.fns.insert(11, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[12], "atan");
        ctx.fns.insert(12, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[13], "log");
        ctx.fns.insert(13, (vec![Type::Float], Type::Float));
        debug_assert_eq!(string_map[14], "pow");
        ctx.fns
            .insert(14, (vec![Type::Float, Type::Float], Type::Float));
        debug_assert_eq!(string_map[15], "atan2");
        ctx.fns
            .insert(15, (vec![Type::Float, Type::Float], Type::Float));
        debug_assert_eq!(string_map[16], "to_float");
        ctx.fns.insert(16, (vec![Type::Int], Type::Float));
        debug_assert_eq!(string_map[17], "to_int");
        ctx.fns.insert(17, (vec![Type::Float], Type::Int));
        debug_assert_eq!(string_map[18], "args");
        ctx.vars.insert(18, Type::Array(Box::new(Type::Int), 1));
        debug_assert_eq!(string_map[19], "argnum");
        ctx.vars.insert(19, Type::Int);

        ctx
    }

    fn check_struct(&self, name: usize) -> Result<()> {
        if self.structs.contains_key(&name) {
            bail!("struct {} exists", self.string_map[name])
        }
        Ok(())
    }

    fn check_fn(&self, name: usize) -> Result<()> {
        if self.fns.contains_key(&name) {
            bail!("function {} exists", self.string_map[name])
        }
        Ok(())
    }

    fn check_var(&self, name: usize) -> Result<()> {
        if self.vars.contains_key(&name) {
            bail!("variable {} exists", self.string_map[name])
        }
        Ok(())
    }

    fn check_temporary_var(&self, name: usize) -> Result<()> {
        if self.temporary_vars.contains_key(&name) {
            bail!("variable {} exists", self.string_map[name])
        }
        Ok(())
    }

    fn insert_struct(&mut self, name: usize, data: Vec<Field>) -> Result<()> {
        self.check_var(name)
            .and(self.check_temporary_var(name))
            .and(self.check_fn(name))
            .with_context(|| format!("could not define struct {}", self.string_map[name]))?;

        if self.structs.insert(name, data).is_some() {
            bail!("duplicate struct identifier {}", self.string_map[name]);
        }

        Ok(())
    }

    fn insert_var(&mut self, name: usize, data: Type) -> Result<()> {
        self.check_temporary_var(name)
            .and(self.check_fn(name))
            .and(self.check_struct(name))
            .with_context(|| format!("could not define variable {}", self.string_map[name]))?;

        if self.vars.insert(name, data).is_some() {
            bail!("duplicate variable identifier {}", self.string_map[name]);
        }

        Ok(())
    }

    fn insert_fn(&mut self, name: usize, data: (Vec<Type>, Type)) -> Result<()> {
        self.check_var(name)
            .and(self.check_temporary_var(name))
            .and(self.check_struct(name))
            .with_context(|| format!("could not define function {}", self.string_map[name]))?;

        if self.fns.insert(name, data).is_some() {
            bail!("duplicate function identifier {}", self.string_map[name]);
        }

        Ok(())
    }

    fn insert_temporary_var(&mut self, name: usize, data: Type) -> Result<()> {
        self.check_var(name)
            .and(self.check_fn(name))
            .and(self.check_struct(name))
            .with_context(|| format!("could not define variable {}", self.string_map[name]))?;

        if self.temporary_vars.insert(name, data).is_some() {
            bail!("duplicate variable identifier {}", self.string_map[name]);
        }

        Ok(())
    }

    fn check_self_referential_struct(&self, ty: &Type) -> Result<()> {
        match ty {
            Type::Struct(Variable(name)) if !self.structs.contains_key(name) => Err(anyhow!(
                "struct definition references nonexistent struct {}",
                self.string_map[*name]
            )),
            Type::Array(ty, _) => self.check_self_referential_struct(ty),
            _ => Ok(()),
        }
    }
}

trait TypeFill {
    fn typefill(&mut self, ctx: &mut Ctx) -> Result<()>;
}

#[allow(clippy::too_many_lines)]
impl TypeFill for Cmd {
    fn typefill(&mut self, ctx: &mut Ctx) -> Result<()> {
        match self {
            Cmd::Show(expr) => expr.typefill(ctx)?,
            Cmd::Struct(Variable(v), fields) => {
                let mut name_check = Vec::with_capacity(fields.len());

                for Field(name, ty) in fields.iter_mut() {
                    ctx.check_self_referential_struct(ty)?;
                    if name_check.contains(name) {
                        bail!("duplicate field identifier {}", ctx.string_map[*v]);
                    }
                    name_check.push(*name);
                }

                ctx.insert_struct(*v, fields.clone())?;
            }
            Cmd::Let(lv, expr) => {
                let expr_type = expr.typefill_get_type(ctx)?;
                match (lv, &expr_type) {
                    (LValue::Var(Variable(v)), _) => ctx.insert_var(*v, expr_type)?,
                    (LValue::Array(Variable(v), dim_bindings), Type::Array(_, dims)) => {
                        ensure!(
                            *dims as usize == dim_bindings.len(),
                            "cannot bind array length bindings {:?} to array of dimension {}",
                            dim_bindings,
                            dims
                        );

                        ctx.insert_var(*v, expr_type)?;

                        for Variable(bind) in dim_bindings {
                            ctx.insert_var(*bind, Type::Int)?;
                        }
                    }
                    (lv, expr_type) => bail!("binding mismatch! {:?} {:?}", lv, expr_type),
                }
            }
            Cmd::Fn(Variable(v), bindings, ty, stmts) => {
                ctx.insert_fn(
                    *v,
                    (
                        bindings.iter().map(|Binding(_, ty)| ty.clone()).collect(),
                        ty.clone(),
                    ),
                )?;

                for Binding(lv, ty) in bindings.iter() {
                    match lv {
                        LValue::Var(Variable(v)) => ctx.insert_temporary_var(*v, ty.clone())?,
                        LValue::Array(Variable(v), dim_bindings) => {
                            ctx.insert_temporary_var(*v, ty.clone())?;

                            for Variable(bind) in dim_bindings {
                                ctx.insert_temporary_var(*bind, Type::Int)?;
                            }
                        }
                    }
                }

                let mut has_return = false;

                for stmt in stmts {
                    match stmt {
                        Statement::Return(expr) => {
                            has_return = true;
                            let expr_type = expr.typefill_get_type(ctx)?;
                            ensure!(
                                expr_type == *ty,
                                "return statment expected to return {:?}, returns {:?}",
                                ty,
                                expr_type
                            );
                        }
                        Statement::Assert(expr, _) => {
                            let expr_type = expr.typefill_get_type(ctx)?;
                            ensure!(
                                expr_type == Type::Bool,
                                "assert statement requires a bool, got {:?}",
                                expr_type
                            );
                        }
                        Statement::Let(lv, expr) => {
                            let expr_type = expr.typefill_get_type(ctx)?;
                            match (lv, &expr_type) {
                                (LValue::Var(Variable(v)), _) => {
                                    ctx.insert_temporary_var(*v, expr_type)?;
                                }
                                (
                                    LValue::Array(Variable(v), dim_bindings),
                                    Type::Array(_, dims),
                                ) => {
                                    ensure!(
                                        *dims as usize == dim_bindings.len(),
                                        "cannot bind array length bindings {:?} to array of dimension {}",
                                        dim_bindings,
                                        dims
                                    );

                                    ctx.insert_temporary_var(*v, expr_type)?;

                                    for Variable(bind) in dim_bindings {
                                        ctx.insert_temporary_var(*bind, Type::Int)?;
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
            }
            Cmd::Write(expr, _) => {
                let expr_type = expr.typefill_get_type(ctx)?;
                match expr_type {
                    Type::Array(ty, 2) if *ty == Type::Struct(Variable(0)) => {}
                    ty => bail!("write takes rgba[,], found {:?}", ty),
                }
            }
            Cmd::Read(_, lv) => {
                let dims = 2;
                let expr_type = Type::Array(Box::new(Type::Struct(Variable(0))), 2);
                match lv {
                    LValue::Var(Variable(v)) => ctx.insert_var(*v, expr_type)?,
                    LValue::Array(Variable(v), dim_bindings) => {
                        ensure!(
                            dims == dim_bindings.len(),
                            "cannot bind array length bindings {:?} to array of dimension {}",
                            dim_bindings,
                            dims
                        );

                        ctx.insert_var(*v, expr_type)?;

                        for Variable(bind) in dim_bindings {
                            ctx.insert_var(*bind, Type::Int)?;
                        }
                    }
                }
            }
            Cmd::Time(cmd) => cmd.typefill(ctx)?,
            Cmd::Assert(expr, _) => {
                let expr_type = expr.typefill_get_type(ctx)?;
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

impl Expr {
    fn typefill_get_type(&mut self, ctx: &mut Ctx) -> Result<Type> {
        self.typefill(ctx)?;
        Ok(self.get_type())
    }
}

#[allow(clippy::too_many_lines)]
impl TypeFill for Expr {
    fn typefill(&mut self, ctx: &mut Ctx) -> Result<()> {
        match self {
            Expr::Int(_, _) | Expr::Float(_, _) | Expr::True | Expr::False | Expr::Void => {}
            Expr::Binop(lhs, op, rhs, ret_ty) => {
                let lhs_type = lhs.typefill_get_type(ctx)?;
                let rhs_type = rhs.typefill_get_type(ctx)?;
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
                        "cannot perform binary operation {:?} {:?} {:?}",
                        lhs_type,
                        op,
                        rhs_type
                    ),
                }
            }
            Expr::Unop(op, expr, ret_ty) => {
                expr.typefill(ctx)?;
                let expr_type = expr.get_type();
                *ret_ty = match (&op, &expr_type) {
                    (Op(TokenType::Not), Type::Bool)
                    | (Op(TokenType::Sub), Type::Int | Type::Float) => expr_type,
                    _ => bail!("cannot perform unary operation {:?} {:?}", op, expr_type),
                }
            }
            Expr::Paren(expr) => expr.typefill(ctx)?,
            Expr::ArrayIndex(array, indexes, ret_ty) => {
                let array = array.typefill_get_type(ctx)?;
                match array {
                    Type::Array(ty, dims) => {
                        ensure!(
                            indexes.len() as u8 == dims,
                            "cannot index {} dimensional array with {} indices",
                            dims,
                            indexes.len()
                        );

                        *ret_ty = *ty;
                    }
                    ty => bail!("cannot array index non array, found {:#?}", ty),
                }

                for index in indexes {
                    index.typefill(ctx)?;
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
                    expr.typefill(ctx)?;
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
                    expr.typefill(ctx)?;
                }

                let Some(struct_type) = ctx.structs.get(v) else {
                    bail!("struct of type {} is not defined", ctx.string_map[*v])
                };

                *ty = Type::Struct(Variable(*v));

                for (expr_type, Field(Variable(fv), field_type)) in
                    exprs.iter().map(Expr::get_type).zip(struct_type.iter())
                {
                    ensure!(
                        expr_type == *field_type,
                        "struct field {} is of type {:?}, received {:?}",
                        ctx.string_map[*fv],
                        field_type,
                        expr_type
                    );
                }
            }
            Expr::Dot(expr, Variable(v), ty) => {
                let struct_name = match expr.typefill_get_type(ctx)? {
                    Type::Struct(Variable(struct_name)) => struct_name,
                    t => bail!("cannot perform operation `.` on non struct {:?}", t),
                };

                let Some(fields) = ctx.structs.get(&struct_name) else {
                    bail!("struct of type {} is not defined", ctx.string_map[*v]);
                };

                let Some(Field(_, fty)) = fields.iter().find(|Field(Variable(fv), _)| fv == v)
                else {
                    bail!(
                        "field {} does not exist on struct of type {}",
                        ctx.string_map[*v],
                        ctx.string_map[struct_name]
                    );
                };

                *ty = fty.clone();
            }
            Expr::Call(Variable(v), exprs, ty) => {
                for expr in exprs.iter_mut() {
                    expr.typefill(ctx)?;
                }

                let Some((args, ret_type)) = ctx.fns.get(v) else {
                    bail!("struct of type {} is not defined", ctx.string_map[*v]);
                };

                match exprs.len().cmp(&args.len()) {
                    Ordering::Less => {
                        bail!(
                            "too few arguments passed to function {}",
                            ctx.string_map[*v]
                        )
                    }
                    Ordering::Greater => {
                        bail!(
                            "too many arguments passed to function {}",
                            ctx.string_map[*v]
                        )
                    }
                    Ordering::Equal => {}
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
                cond.typefill(ctx)?;
                let cond_type = cond.get_type();
                ensure!(
                    matches!(cond_type, Type::Bool),
                    "condition in if expression must be a boolean, found {:?}",
                    cond_type
                );

                r#true.typefill(ctx)?;
                let true_type = r#true.get_type();
                r#false.typefill(ctx)?;
                let false_type = r#false.get_type();

                ensure!(
                    true_type == false_type,
                    "both branches of an if expression must match types. Found {:?} and {:?}",
                    true_type,
                    false_type
                );

                *ty = true_type;
            }
            Expr::Variable(Variable(v), ret_ty) => {
                let Some(ty) = ctx.vars.get(v).or_else(|| ctx.temporary_vars.get(v)) else {
                    bail!("variable {} is undefined", ctx.string_map[*v]);
                };

                *ret_ty = ty.clone();
            }
            Expr::ArrayLoop(fields, expr, ret_ty) => {
                ensure!(!fields.is_empty(), "loops require at least one field");

                for LoopField(_, le) in fields.iter_mut() {
                    let le = le.typefill_get_type(ctx)?;
                    ensure!(
                        le == Type::Int,
                        "can only loop over integers, found {:?}",
                        le
                    );
                }

                for LoopField(Variable(lv), le) in fields.iter_mut() {
                    ctx.insert_var(*lv, le.get_type())?;
                }

                expr.typefill(ctx)?;
                *ret_ty = Type::Array(Box::new(expr.get_type()), fields.len() as u8);

                for LoopField(Variable(lv), _) in fields {
                    ctx.vars.remove(lv);
                }
            }
            Expr::SumLoop(fields, expr, ret_ty) => {
                ensure!(!fields.is_empty(), "loops require at least one field");

                for LoopField(_, le) in fields.iter_mut() {
                    le.typefill(ctx)?;
                    ensure!(
                        le.get_type() == Type::Int,
                        "can only loop over integers, found {:?}",
                        le.get_type()
                    );
                }

                for LoopField(Variable(lv), le) in fields.iter_mut() {
                    ctx.insert_var(*lv, le.get_type())?;
                }

                expr.typefill(ctx)?;
                *ret_ty = expr.get_type();

                ensure!(
                    matches!(ret_ty, Type::Int | Type::Float),
                    "you can only sum to an integer or float, found {:?}",
                    ret_ty
                );

                for LoopField(Variable(lv), _) in fields {
                    ctx.vars.remove(lv);
                }
            }
        }

        Ok(())
    }
}

/// # Errors
pub fn typecheck(cmds: &mut [Cmd], string_map: &[&str], _tokens_consumed: &[usize]) -> Result<()> {
    let mut ctx = Ctx::new(string_map);

    for cmd in cmds {
        cmd.typefill(&mut ctx).inspect_err(|_| {})?;
        ctx.temporary_vars.clear();
    }

    PRINT_TYPES.with(|print_types| print_types.set(true));

    Ok(())
}
