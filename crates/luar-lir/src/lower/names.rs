//! The names a body mentions and the names it writes.

use luar_ast::{
    ArmBody, Block, Expr, ExprKind, FunctionBody, InterpolationPart, MapKey, Stmt, StmtKind,
};

/// Collects every name `block` mentions, in the order it mentions them.
pub(super) fn in_block(block: &Block, out: &mut Vec<String>) {
    walk_block(block, &mut Mentioned(out));
}

/// The names `block` assigns to, anywhere inside it, including inside a
/// closure written in it.
pub(super) fn assigned(block: &Block, out: &mut Vec<String>) {
    walk_block(block, &mut Assigned(out));
}

/// The names a closure in `block` mentions that something in `block` assigns
/// to, inside a closure or not. Every holder of one reads and writes the same
/// cell (LR9.8).
pub(super) fn shared(block: &Block) -> Vec<String> {
    let mut captured = Vec::new();
    walk_block(block, &mut Captured(&mut captured));
    let mut written = Vec::new();
    assigned(block, &mut written);
    captured.retain(|name| written.contains(name));
    captured.sort();
    captured.dedup();
    captured
}

struct Mentioned<'a>(&'a mut Vec<String>);

impl Visit for Mentioned<'_> {
    fn expr(&mut self, expr: &Expr) {
        if let ExprKind::Name(name) = &expr.kind {
            self.0.push(name.clone());
        }
    }
}

struct Assigned<'a>(&'a mut Vec<String>);

impl Visit for Assigned<'_> {
    fn stmt(&mut self, stmt: &Stmt) {
        if let StmtKind::Assign { target, .. } = &stmt.kind
            && let ExprKind::Name(name) = &target.kind
        {
            self.0.push(name.clone());
        }
    }
}

struct Captured<'a>(&'a mut Vec<String>);

impl Visit for Captured<'_> {
    fn expr(&mut self, expr: &Expr) {
        if let ExprKind::Function { body, .. } = &expr.kind {
            match body.as_ref() {
                FunctionBody::Block(body) => in_block(body, self.0),
                FunctionBody::Expr(value) => walk_expr(value, &mut Mentioned(self.0)),
            }
        }
    }
}

trait Visit {
    fn stmt(&mut self, _stmt: &Stmt) {}
    fn expr(&mut self, _expr: &Expr) {}
}

fn walk_block(block: &Block, visit: &mut impl Visit) {
    for stmt in &block.stmts {
        walk_stmt(stmt, visit);
    }
}

fn walk_stmt(stmt: &Stmt, visit: &mut impl Visit) {
    visit.stmt(stmt);
    match &stmt.kind {
        StmtKind::Local { value, .. } => {
            if let Some(value) = value {
                walk_expr(value, visit);
            }
        }
        StmtKind::Const { value, .. } => walk_expr(value, visit),
        StmtKind::Assign { target, value, .. } => {
            walk_expr(target, visit);
            walk_expr(value, visit);
        }
        StmtKind::If {
            branches,
            otherwise,
        } => {
            for branch in branches {
                walk_expr(&branch.condition, visit);
                walk_block(&branch.body, visit);
            }
            if let Some(otherwise) = otherwise {
                walk_block(otherwise, visit);
            }
        }
        StmtKind::While {
            condition, body, ..
        } => {
            walk_expr(condition, visit);
            walk_block(body, visit);
        }
        StmtKind::Repeat { body, until, .. } => {
            walk_block(body, visit);
            walk_expr(until, visit);
        }
        StmtKind::For { iterable, body, .. } => {
            walk_expr(iterable, visit);
            walk_block(body, visit);
        }
        StmtKind::Unsafe(body) => walk_block(body, visit),
        StmtKind::Defer(expr) | StmtKind::Expr(expr) => walk_expr(expr, visit),
        StmtKind::Match { scrutinee, arms } => {
            walk_expr(scrutinee, visit);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    walk_expr(guard, visit);
                }
                match &arm.body {
                    ArmBody::Block(body) => walk_block(body, visit),
                    ArmBody::Expr(value) => walk_expr(value, visit),
                }
            }
        }
        StmtKind::Return(value) => {
            if let Some(value) = value {
                walk_expr(value, visit);
            }
        }
        StmtKind::Throw(value) => walk_expr(value, visit),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            walk_block(body, visit);
            for clause in catches {
                walk_block(&clause.body, visit);
            }
            if let Some(finally) = finally {
                walk_block(finally, visit);
            }
        }
        StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Error => {}
    }
}

fn walk_expr(expr: &Expr, visit: &mut impl Visit) {
    visit.expr(expr);
    match &expr.kind {
        ExprKind::Unary { operand, .. } => walk_expr(operand, visit),
        ExprKind::Binary { left, right, .. } => {
            walk_expr(left, visit);
            walk_expr(right, visit);
        }
        ExprKind::Range { start, end, .. } => {
            for bound in [start, end].into_iter().flatten() {
                walk_expr(bound, visit);
            }
        }
        ExprKind::Call { callee, args, .. } => {
            walk_expr(callee, visit);
            for argument in args {
                walk_expr(&argument.value, visit);
            }
        }
        ExprKind::Field { receiver, .. } => walk_expr(receiver, visit),
        ExprKind::Index {
            receiver, index, ..
        } => {
            walk_expr(receiver, visit);
            walk_expr(index, visit);
        }
        ExprKind::Try(inner)
        | ExprKind::Await(inner)
        | ExprKind::AddressOf { operand: inner, .. } => walk_expr(inner, visit),
        ExprKind::Cast { value, .. } | ExprKind::TypeTest { value, .. } => walk_expr(value, visit),
        ExprKind::Tuple(members) | ExprKind::List(members) | ExprKind::Set(members) => {
            for member in members {
                walk_expr(member, visit);
            }
        }
        ExprKind::Record { fields, .. } => {
            for field in fields {
                walk_expr(&field.value, visit);
            }
        }
        ExprKind::Map(entries) => {
            for entry in entries {
                if let MapKey::Computed(key) = &entry.key {
                    walk_expr(key, visit);
                }
                walk_expr(&entry.value, visit);
            }
        }
        ExprKind::Interpolation(parts) => {
            for part in parts {
                if let InterpolationPart::Expr(part) = part {
                    walk_expr(part, visit);
                }
            }
        }
        // A closure inside a closure reaches the outer function through the
        // one around it, so its names count too (LR9.8).
        ExprKind::Function { params, body, .. } => {
            for param in params {
                if let Some(default) = &param.default {
                    walk_expr(default, visit);
                }
            }
            match body.as_ref() {
                FunctionBody::Block(body) => walk_block(body, visit),
                FunctionBody::Expr(value) => walk_expr(value, visit),
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            walk_expr(scrutinee, visit);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    walk_expr(guard, visit);
                }
                match &arm.body {
                    ArmBody::Block(body) => walk_block(body, visit),
                    ArmBody::Expr(value) => walk_expr(value, visit),
                }
            }
        }
        ExprKind::If {
            branches,
            otherwise,
        } => {
            for (condition, value) in branches {
                walk_expr(condition, visit);
                walk_expr(value, visit);
            }
            walk_expr(otherwise, visit);
        }

        ExprKind::Name(_)
        | ExprKind::Nil
        | ExprKind::Bool(_)
        | ExprKind::Integer(_)
        | ExprKind::Float(_)
        | ExprKind::String(_)
        | ExprKind::ByteString(_)
        | ExprKind::Char(_)
        | ExprKind::Error => {}
    }
}
