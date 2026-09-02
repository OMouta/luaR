//! Which functions an exception can escape (LR25.3).
//!
//! Exceptions do not appear in signatures, so the set is worked out from the
//! whole program: a function throws if it writes a `throw` nothing around it
//! catches, or if it calls one that does. Calling into itself makes that
//! circular, so the set grows a round at a time until it stops growing.

use std::collections::HashSet;

use luar_ast::{ArmBody, Block, Expr, ExprKind, InterpolationPart, MapKey, Stmt, StmtKind};
use luar_diagnostics::Span;
use luar_sema::facts::Facts;
use luar_sema::modules::ModuleId;
use luar_sema::types::Type;

/// The declarations an exception can escape, by the span of each.
pub(super) fn escaping(
    bodies: &[(Span, Block)],
    facts: &Facts,
    interfaces: &HashSet<(ModuleId, String)>,
) -> HashSet<Span> {
    let mut throwing: HashSet<Span> = HashSet::new();

    loop {
        let found: Vec<Span> = bodies
            .iter()
            .filter(|(span, body)| {
                !throwing.contains(span)
                    && Scan {
                        facts,
                        throwing: &throwing,
                        interfaces,
                    }
                    .block(body)
            })
            .map(|(span, _)| *span)
            .collect();

        if found.is_empty() {
            return throwing;
        }
        throwing.extend(found);
    }
}

struct Scan<'a> {
    facts: &'a Facts,
    /// The declarations already known to throw. It only ever grows, so an
    /// answer of `true` stays true in later rounds.
    throwing: &'a HashSet<Span>,
    interfaces: &'a HashSet<(ModuleId, String)>,
}

impl Scan<'_> {
    fn block(&self, block: &Block) -> bool {
        block.stmts.iter().any(|stmt| self.stmt(stmt))
    }

    fn stmt(&self, stmt: &Stmt) -> bool {
        match &stmt.kind {
            StmtKind::Throw(value) => {
                let _ = self.expr(value);
                true
            }
            // LR25.3: a clause with no type catches whatever the body threw,
            // so only what the clauses and the `finally` throw gets out.
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                let caught = catches.iter().any(|clause| clause.ty.is_none());
                (self.block(body) && !caught)
                    || catches.iter().any(|clause| self.block(&clause.body))
                    || finally.as_ref().is_some_and(|block| self.block(block))
            }
            StmtKind::Local { value, .. } => value.as_ref().is_some_and(|value| self.expr(value)),
            StmtKind::Const { value, .. } => self.expr(value),
            StmtKind::Assign { target, value, .. } => self.expr(target) || self.expr(value),
            StmtKind::If {
                branches,
                otherwise,
            } => {
                branches
                    .iter()
                    .any(|branch| self.expr(&branch.condition) || self.block(&branch.body))
                    || otherwise.as_ref().is_some_and(|block| self.block(block))
            }
            StmtKind::While {
                condition, body, ..
            } => self.expr(condition) || self.block(body),
            StmtKind::Repeat { body, until, .. } => self.block(body) || self.expr(until),
            StmtKind::For { iterable, body, .. } => self.expr(iterable) || self.block(body),
            StmtKind::Unsafe(body) => self.block(body),
            StmtKind::Defer(value) | StmtKind::Expr(value) => self.expr(value),
            StmtKind::Match { scrutinee, arms } => {
                self.expr(scrutinee)
                    || arms.iter().any(|arm| {
                        arm.guard.as_ref().is_some_and(|guard| self.expr(guard))
                            || match &arm.body {
                                ArmBody::Block(body) => self.block(body),
                                ArmBody::Expr(value) => self.expr(value),
                            }
                    })
            }
            StmtKind::Return(value) => value.as_ref().is_some_and(|value| self.expr(value)),
            StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Error => false,
        }
    }

    fn expr(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Call {
                callee,
                method,
                args,
                ..
            } => {
                self.reaches_a_throw(expr.span)
                    || (method.is_some() && self.is_interface(callee))
                    || (self.facts.call(expr.span).is_none()
                        && self.facts.builtin(expr.span).is_none()
                        && matches!(self.facts.type_of(callee.span), Some(Type::Function { .. })))
                    || self.expr(callee)
                    || args.iter().any(|argument| self.expr(&argument.value))
            }
            ExprKind::Unary { operand, .. } => self.expr(operand),
            ExprKind::Binary { left, right, .. } => self.expr(left) || self.expr(right),
            ExprKind::Range { start, end, .. } => [start, end]
                .into_iter()
                .flatten()
                .any(|bound| self.expr(bound)),
            ExprKind::Field { receiver, .. } => self.expr(receiver),
            ExprKind::Index {
                receiver, index, ..
            } => self.expr(receiver) || self.expr(index),
            ExprKind::Await(_) => true,
            ExprKind::Try(inner) | ExprKind::AddressOf { operand: inner, .. } => self.expr(inner),
            ExprKind::Cast { value, .. } | ExprKind::TypeTest { value, .. } => self.expr(value),
            ExprKind::Tuple(members) | ExprKind::List(members) | ExprKind::Set(members) => {
                members.iter().any(|member| self.expr(member))
            }
            ExprKind::Record { fields, .. } => fields.iter().any(|field| self.expr(&field.value)),
            ExprKind::Map(entries) => entries.iter().any(|entry| {
                matches!(&entry.key, MapKey::Computed(key) if self.expr(key))
                    || self.expr(&entry.value)
            }),
            ExprKind::Interpolation(parts) => parts.iter().any(|part| match part {
                InterpolationPart::Expr(part) => self.expr(part),
                InterpolationPart::Text(_) => false,
            }),
            // A closure runs where it is called, not where it is written, so
            // what it throws belongs to whoever calls it.
            ExprKind::Function { params, .. } => params
                .iter()
                .any(|param| param.default.as_ref().is_some_and(|value| self.expr(value))),
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee)
                    || arms.iter().any(|arm| {
                        arm.guard.as_ref().is_some_and(|guard| self.expr(guard))
                            || match &arm.body {
                                ArmBody::Block(body) => self.block(body),
                                ArmBody::Expr(value) => self.expr(value),
                            }
                    })
            }
            ExprKind::If {
                branches,
                otherwise,
            } => {
                branches
                    .iter()
                    .any(|(condition, value)| self.expr(condition) || self.expr(value))
                    || self.expr(otherwise)
            }
            ExprKind::Nil
            | ExprKind::Bool(_)
            | ExprKind::Integer(_)
            | ExprKind::Float(_)
            | ExprKind::String(_)
            | ExprKind::ByteString(_)
            | ExprKind::Char(_)
            | ExprKind::Name(_)
            | ExprKind::Error => false,
        }
    }

    /// Whether the call at `span` reaches a declaration that throws.
    fn reaches_a_throw(&self, span: Span) -> bool {
        self.facts
            .call(span)
            .is_some_and(|declaration| self.throwing.contains(&declaration))
    }

    fn is_interface(&self, receiver: &Expr) -> bool {
        matches!(
            self.facts.type_of(receiver.span),
            Some(Type::Named { module, name, .. })
                if self.interfaces.contains(&(*module, name.clone()))
        ) || matches!(
            self.facts.type_of(receiver.span),
            Some(Type::Parameter(_) | Type::Intersection(_))
        )
    }
}
