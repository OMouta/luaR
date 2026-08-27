//! Every name a body writes.

use luar_ast::{
    ArmBody, Block, Expr, ExprKind, FunctionBody, InterpolationPart, MapKey, Stmt, StmtKind,
};

/// Collects every name `block` mentions, in the order it mentions them.
pub(super) fn in_block(block: &Block, out: &mut Vec<String>) {
    for stmt in &block.stmts {
        in_stmt(stmt, out);
    }
}

fn in_stmt(stmt: &Stmt, out: &mut Vec<String>) {
    match &stmt.kind {
        StmtKind::Local { value, .. } => {
            if let Some(value) = value {
                in_expr(value, out);
            }
        }
        StmtKind::Const { value, .. } => in_expr(value, out),
        StmtKind::Assign { target, value, .. } => {
            in_expr(target, out);
            in_expr(value, out);
        }
        StmtKind::If {
            branches,
            otherwise,
        } => {
            for branch in branches {
                in_expr(&branch.condition, out);
                in_block(&branch.body, out);
            }
            if let Some(otherwise) = otherwise {
                in_block(otherwise, out);
            }
        }
        StmtKind::While {
            condition, body, ..
        } => {
            in_expr(condition, out);
            in_block(body, out);
        }
        StmtKind::Repeat { body, until, .. } => {
            in_block(body, out);
            in_expr(until, out);
        }
        StmtKind::For { iterable, body, .. } => {
            in_expr(iterable, out);
            in_block(body, out);
        }
        StmtKind::Conditional {
            branches,
            otherwise,
        } => {
            for (condition, body) in branches {
                in_expr(condition, out);
                in_block(body, out);
            }
            if let Some(otherwise) = otherwise {
                in_block(otherwise, out);
            }
        }
        StmtKind::Unsafe(body) => in_block(body, out),
        StmtKind::Defer(expr) | StmtKind::Expr(expr) => in_expr(expr, out),
        StmtKind::Match { scrutinee, arms } => {
            in_expr(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    in_expr(guard, out);
                }
                match &arm.body {
                    ArmBody::Block(body) => in_block(body, out),
                    ArmBody::Expr(value) => in_expr(value, out),
                }
            }
        }
        StmtKind::Return(value) => {
            if let Some(value) = value {
                in_expr(value, out);
            }
        }
        StmtKind::Throw(value) => in_expr(value, out),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            in_block(body, out);
            for clause in catches {
                in_block(&clause.body, out);
            }
            if let Some(finally) = finally {
                in_block(finally, out);
            }
        }
        StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Error => {}
    }
}

fn in_expr(expr: &Expr, out: &mut Vec<String>) {
    match &expr.kind {
        ExprKind::Name(name) => out.push(name.clone()),

        ExprKind::Unary { operand, .. } => in_expr(operand, out),
        ExprKind::Binary { left, right, .. } => {
            in_expr(left, out);
            in_expr(right, out);
        }
        ExprKind::Range { start, end, .. } => {
            for bound in [start, end].into_iter().flatten() {
                in_expr(bound, out);
            }
        }
        ExprKind::Call { callee, args, .. } => {
            in_expr(callee, out);
            for argument in args {
                in_expr(&argument.value, out);
            }
        }
        ExprKind::Field { receiver, .. } => in_expr(receiver, out),
        ExprKind::Index {
            receiver, index, ..
        } => {
            in_expr(receiver, out);
            in_expr(index, out);
        }
        ExprKind::Try(inner)
        | ExprKind::Await(inner)
        | ExprKind::AddressOf { operand: inner, .. } => in_expr(inner, out),
        ExprKind::Cast { value, .. } | ExprKind::TypeTest { value, .. } => in_expr(value, out),
        ExprKind::Tuple(members) | ExprKind::List(members) => {
            for member in members {
                in_expr(member, out);
            }
        }
        ExprKind::Record { fields, .. } => {
            for field in fields {
                in_expr(&field.value, out);
            }
        }
        ExprKind::Map(entries) => {
            for entry in entries {
                if let MapKey::Computed(key) = &entry.key {
                    in_expr(key, out);
                }
                in_expr(&entry.value, out);
            }
        }
        ExprKind::Interpolation(parts) => {
            for part in parts {
                if let InterpolationPart::Expr(part) = part {
                    in_expr(part, out);
                }
            }
        }
        // A closure inside a closure reaches the outer function through the
        // one around it, so its names count too (LR9.8).
        ExprKind::Function { params, body, .. } => {
            for param in params {
                if let Some(default) = &param.default {
                    in_expr(default, out);
                }
            }
            match body.as_ref() {
                FunctionBody::Block(body) => in_block(body, out),
                FunctionBody::Expr(value) => in_expr(value, out),
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            in_expr(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    in_expr(guard, out);
                }
                match &arm.body {
                    ArmBody::Block(body) => in_block(body, out),
                    ArmBody::Expr(value) => in_expr(value, out),
                }
            }
        }
        ExprKind::If {
            branches,
            otherwise,
        } => {
            for (condition, value) in branches {
                in_expr(condition, out);
                in_expr(value, out);
            }
            in_expr(otherwise, out);
        }

        ExprKind::Nil
        | ExprKind::Bool(_)
        | ExprKind::Integer(_)
        | ExprKind::Float(_)
        | ExprKind::String(_)
        | ExprKind::ByteString(_)
        | ExprKind::Char(_)
        | ExprKind::Error => {}
    }
}
