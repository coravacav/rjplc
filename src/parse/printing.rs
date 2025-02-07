use super::{
    Binding, Cmd, Expr, Field, LValue, LiteralString, LoopField, Op, Statement, TokenType, Type,
    Variable, Write,
};
use crate::CustomDisplay;

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

impl CustomDisplay for Variable {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        f.write_str(string_map[self.0])
    }
}
impl CustomDisplay for LiteralString {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        f.write_char('"')?;
        f.write_str(string_map[self.0])?;
        f.write_char('"')
    }
}
impl CustomDisplay for LoopField {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        self.0.fmt(f, string_map)?;
        f.write_char(' ')?;
        self.1.fmt(f, string_map)
    }
}
impl CustomDisplay for Field {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        self.0.fmt(f, string_map)?;
        f.write_char(' ')?;
        self.1.fmt(f, string_map)
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
