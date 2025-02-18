use std::cell::Cell;

use super::{
    Binding, Command, CommandKind, Expr, ExprKind, Field, LValue, LiteralString, LoopField, Op,
    Statement, StatementKind, TokenType, Type, TypeKind, Variable, Write,
};
use crate::{CustomDisplay, PRINT_TYPES};

trait PrintJoined {
    fn print_joined(
        &self,
        f: &mut String,
        string_map: &[&str],
        prefix_if_non_empty: bool,
    ) -> std::fmt::Result;
}

impl<T: CustomDisplay> PrintJoined for [T] {
    fn print_joined(
        &self,
        f: &mut String,
        string_map: &[&str],
        prefix_if_non_empty: bool,
    ) -> std::fmt::Result {
        if prefix_if_non_empty && !self.is_empty() {
            f.write_str(" ")?;
        }

        for (i, t) in self.iter().enumerate() {
            if i != 0 {
                f.write_str(" ")?;
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

/// Necessary? No. Fun? Yes.
macro_rules! disp_help {
    ($f:ident, $string_map:ident, $($x:tt $y:tt),+) => {{
        $(disp_help!(@ $f, $string_map, $x $y);)+
        Ok(())
    }};
    (@ $f:ident, $string_map:ident, str $string:literal) => {
        $f.write_str($string)?;
    };
    (@ $f:ident, $string_map:ident, char $char:literal) => {
        $f.write_char($char)?;
    };
    (@ $f:ident, $string_map:ident, fmt $val:ident) => {
        $val.fmt($f, $string_map)?;
    };
    (@ $f:ident, $string_map:ident, type $val:ident) => {
        $val.fmt_if($f, $string_map)?;
    };
    (@ $f:ident, $string_map:ident, joined $val:ident) => {
        $val.print_joined($f, $string_map, true)?;
    };
    (@ $f:ident, $string_map:ident, joinedns $val:ident) => {
        $val.print_joined($f, $string_map, false)?;
    };
}

impl CustomDisplay for Command {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match &self.kind {
            CommandKind::Read(file, lvalue) => {
                disp_help!(f, string_map, str "(ReadCmd ", fmt file, char ' ', fmt lvalue, char ')')
            }
            CommandKind::Write(expr, file) => {
                disp_help!(f, string_map, str "(WriteCmd ", fmt expr, char ' ', fmt file, char ')')
            }
            CommandKind::Let(lvalue, expr) => {
                disp_help!(f, string_map, str "(LetCmd ", fmt lvalue, char ' ', fmt expr, char ')')
            }
            CommandKind::Assert(expr, msg) => {
                disp_help!(f, string_map, str "(AssertCmd ", fmt expr, char ' ', fmt msg, char ')')
            }
            CommandKind::Print(msg) => {
                disp_help!(f, string_map, str "(PrintCmd ", fmt msg, char ')')
            }
            CommandKind::Show(expr) => {
                disp_help!(f, string_map, str "(ShowCmd ", fmt expr, char ')')
            }
            CommandKind::Time(cmd) => {
                disp_help!(f, string_map, str "(TimeCmd ", fmt cmd, char ')')
            }
            CommandKind::Fn(name, bindings, ty, statements) => {
                disp_help!(f, string_map, str "(FnCmd ", fmt name, str " ((", joinedns bindings, str ")) ", fmt ty, char ' ', joinedns statements, char ')')
            }
            CommandKind::Struct(name, fields) => {
                disp_help!(f, string_map, str "(StructCmd ", fmt name, joined fields, char ')')
            }
        }
    }
}
impl CustomDisplay for Statement {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match &self.kind {
            StatementKind::Let(lvalue, expr) => {
                disp_help!(f, string_map, str "(LetStmt ", fmt lvalue, char ' ', fmt expr, char ')')
            }
            StatementKind::Assert(expr, msg) => {
                disp_help!(f, string_map, str "(AssertStmt ", fmt expr, char ' ', fmt msg, char ')')
            }
            StatementKind::Return(expr) => {
                disp_help!(f, string_map, str "(ReturnStmt ", fmt expr, char ')')
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
        match &self.kind {
            ExprKind::Int(_, i) => {
                let i = {
                    let i = string_map[*i].trim_start_matches('0');
                    if i.is_empty() {
                        "0"
                    } else {
                        i
                    }
                };

                if PRINT_TYPES.with(Cell::get) {
                    write!(f, "(IntExpr (IntType) {i})")
                } else {
                    write!(f, "(IntExpr {i})")
                }
            }
            ExprKind::Float(fl, s_fl) => string_map[*s_fl]
                .split_once('.')
                .map(|(trunc, _)| {
                    let trunc = trunc.trim_start_matches('0');

                    if PRINT_TYPES.with(Cell::get) {
                        if trunc.is_empty() {
                            write!(f, "(FloatExpr (FloatType) 0)")
                        } else if trunc.len() > 15 {
                            write!(f, "(FloatExpr (FloatType) {})", fl.trunc())
                        } else {
                            write!(f, "(FloatExpr (FloatType) {trunc})")
                        }
                    } else if trunc.is_empty() {
                        write!(f, "(FloatExpr 0)")
                    } else if trunc.len() > 15 {
                        write!(f, "(FloatExpr {})", fl.trunc())
                    } else {
                        write!(f, "(FloatExpr {trunc})")
                    }
                })
                .unwrap(),
            ExprKind::True => {
                if PRINT_TYPES.with(Cell::get) {
                    write!(f, "(TrueExpr (BoolType))")
                } else {
                    write!(f, "(TrueExpr)")
                }
            }
            ExprKind::False => {
                if PRINT_TYPES.with(Cell::get) {
                    write!(f, "(FalseExpr (BoolType))")
                } else {
                    write!(f, "(FalseExpr)")
                }
            }
            ExprKind::Void => {
                if PRINT_TYPES.with(Cell::get) {
                    write!(f, "(VoidExpr (VoidType))")
                } else {
                    write!(f, "(VoidExpr)")
                }
            }
            ExprKind::Variable(s, ty) => {
                disp_help!(f, string_map, str "(VarExpr ", type ty, fmt s, char ')')
            }
            ExprKind::Paren(expr) => expr.fmt(f, string_map),
            ExprKind::ArrayLiteral(exprs, ty) => {
                if exprs.is_empty() {
                    f.write_str("(ArrayLiteralExpr)")
                } else {
                    f.write_str("(ArrayLiteralExpr ")?;
                    ty.fmt_if(f, string_map)?;
                    exprs.print_joined(f, string_map, false)?;
                    f.write_char(')')
                }
            }
            ExprKind::ArrayIndex(s, exprs, ty) => {
                disp_help!(f, string_map, str "(ArrayIndexExpr ", type ty, fmt s, joined exprs, char ')')
            }
            ExprKind::Binop(expr, op, expr2, ty) => {
                disp_help!(f, string_map, str "(BinopExpr ", type ty, fmt expr, char ' ', fmt op, char ' ', fmt expr2, char ')')
            }
            ExprKind::Call(expr, exprs, ty) => {
                disp_help!(f, string_map, str "(CallExpr ", type ty, fmt expr, joined exprs, char ')')
            }
            ExprKind::StructLiteral(s, exprs, ty) => {
                disp_help!(f, string_map, str "(StructLiteralExpr ", type ty, fmt s, joined exprs, char ')')
            }
            ExprKind::Dot(expr, s, ty) => {
                disp_help!(f, string_map, str "(DotExpr ", type ty, fmt expr, char ' ', fmt s, char ')')
            }
            ExprKind::Unop(op, expr, ty) => {
                disp_help!(f, string_map, str "(UnopExpr ", type ty, fmt op, char ' ', fmt expr, char ')')
            }
            ExprKind::If(expr, expr2, expr3, ty) => {
                disp_help!(f, string_map, str "(IfExpr ", type ty, fmt expr, char ' ', fmt expr2, char ' ', fmt expr3, char ')')
            }
            ExprKind::ArrayLoop(fields, expr, ty) => {
                f.write_str("(ArrayLoopExpr ")?;
                ty.fmt_if(f, string_map)?;
                if !fields.is_empty() {
                    fields.print_joined(f, string_map, false)?;
                    f.write_char(' ')?;
                }
                expr.fmt(f, string_map)?;
                write!(f, ")")
            }
            ExprKind::SumLoop(fields, expr, ty) => {
                f.write_str("(SumLoopExpr ")?;
                ty.fmt_if(f, string_map)?;
                if !fields.is_empty() {
                    fields.print_joined(f, string_map, false)?;
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
            LValue::Var(s) => disp_help!(f, string_map, str "(VarLValue ", fmt s, char ')'),
            LValue::Array(s, args) => {
                disp_help!(f, string_map, str "(ArrayLValue ", fmt s, char ' ', joinedns args, char ')')
            }
        }
    }
}
impl CustomDisplay for Type {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match &self.kind {
            TypeKind::Struct(Variable(s, _)) => {
                f.write_str("(StructType ")?;
                f.write_str(string_map[*s])?;
                f.write_char(')')
            }
            TypeKind::Array(s, i) => {
                f.write_str("(ArrayType ")?;
                s.fmt(f, string_map)?;
                f.write_char(' ')?;
                write!(f, "{i}")?;
                f.write_char(')')
            }
            TypeKind::Float => f.write_str("(FloatType)"),
            TypeKind::Int => f.write_str("(IntType)"),
            TypeKind::Bool => f.write_str("(BoolType)"),
            TypeKind::Void => f.write_str("(VoidType)"),
            TypeKind::None => Ok(()),
        }
    }
}

impl Type {
    /// # Errors
    pub fn fmt_if(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match &self.kind {
            TypeKind::None => return Ok(()),
            _ => self.fmt(f, string_map)?,
        }
        f.write_char(' ')
    }
}

impl CustomDisplay for Binding {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        let Binding(l, r) = self;
        disp_help!(f, string_map, fmt l, char ' ', fmt r)
    }
}
