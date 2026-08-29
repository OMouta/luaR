//! Statements, and the loop and continue flow through them.

use std::collections::HashSet;

use luar_ast::{ArmBody, Block, Expr, ExprKind, FunctionBody, Item, Stmt, StmtKind};
use luar_diagnostics::{Diagnostic, codes};

use crate::names::bound;
use crate::types::{Builtin, Primitive, Type};

use super::builtins::{is_collection, is_frozen_collection};
use super::operators::{is_numeric, protocol_of, settle, union};
use super::{Checker, ContinueFlow, LoopFlow, Narrowing};

impl Checker<'_> {
    pub(super) fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Local { binding, ty, value } => {
                let declared = ty.as_ref().map(|ty| self.resolve(ty));
                let value_type = value.as_ref().map(|value| {
                    let held = match &declared {
                        Some(declared) => self.expr_wanting(value, declared),
                        None => self.expr(value),
                    };
                    (held, value.span)
                });

                let held = match declared {
                    Some(declared) => {
                        if let Some((value, span)) = &value_type {
                            self.expect(&declared, value, *span);
                        }
                        declared
                    }
                    None => value_type
                        .as_ref()
                        .map_or(Type::Unresolved, |(value, _)| settle(value.clone())),
                };
                let held = self.closure_binding(held, value_type.as_ref().map(|(value, _)| value));

                self.facts.record_binding(stmt.span, held.clone());
                self.declare(binding, held, stmt.span);

                // LR5.1: a binding declared with no value holds nothing until
                // something writes to it.
                if value.is_none() {
                    for name in bound(binding) {
                        self.unwritten.insert(name);
                    }
                }
            }
            StmtKind::Const {
                binding, ty, value, ..
            } => {
                let declared = ty.as_ref().map(|ty| self.resolve(ty));
                let initialized = match &declared {
                    Some(declared) => self.expr_wanting(value, declared),
                    None => self.expr(value),
                };
                let held = match declared {
                    Some(declared) => {
                        self.expect(&declared, &initialized, value.span);
                        declared
                    }
                    None => settle(initialized.clone()),
                };
                let held = self.closure_binding(held, Some(&initialized));

                self.facts.record_binding(stmt.span, held.clone());
                self.declare(binding, held, stmt.span);
                self.bind_constant(binding);
                self.evaluable(value);
            }
            StmtKind::Assign { target, op, value } => {
                // LR57: what a branch proved narrows what the name reads as,
                // and never what may be written to it.
                let wanted = match &target.kind {
                    ExprKind::Name(name) => self.unnarrowed(name),
                    _ => self.expr(target),
                };
                if let ExprKind::Index { receiver, .. } = &target.kind
                    && self
                        .facts
                        .type_of(receiver.span)
                        .is_some_and(is_frozen_collection)
                {
                    self.diagnostics.push(Diagnostic::error(
                        codes::WRITE_TO_FROZEN_COLLECTION,
                        target.span,
                        "a frozen collection cannot be assigned through",
                    ));
                }
                // LR13: `length` is not a field.
                if let ExprKind::Field { receiver, name, .. } = &target.kind
                    && name == "length"
                    && self.facts.type_of(receiver.span).is_some_and(is_collection)
                {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::INVALID_ASSIGNMENT_TARGET,
                            target.span,
                            "`length` cannot be assigned",
                        )
                        .note("Assignment writes to a name, a field, or an element (LR89.2)."),
                    );
                }
                if let ExprKind::Name(name) = &target.kind {
                    self.mark_capture_mutable(name);
                }
                let held = self.expr(value);
                if let ExprKind::Name(name) = &target.kind {
                    self.update_closure_binding(name, &held);
                }

                // LR5.4, LR36: a compound assignment applies the operator it
                // contains, so a type that operator is not built in for
                // applies it through the protocol it names.
                let produced = match op {
                    Some(op) if !is_numeric(&wanted) => {
                        protocol_of(*op).map(|(spelling, protocol, method)| {
                            self.overloaded(
                                spelling,
                                protocol,
                                method,
                                &wanted,
                                Some((&held, value.span)),
                                target.span,
                            )
                        })
                    }
                    _ => None,
                };

                self.expect(&wanted, produced.as_ref().unwrap_or(&held), value.span);

                if let ExprKind::Name(name) = &target.kind {
                    // LR5.2: `const` binds once, and it is the binding that is
                    // immutable, whatever the value it holds allows.
                    if self.is_constant(name) {
                        self.diagnostics.push(
                            Diagnostic::error(
                                codes::ASSIGN_TO_CONSTANT,
                                target.span,
                                format!("`{name}` is bound by `const`"),
                            )
                            .note("A `const` binding is never bound again (LR5.2)."),
                        );
                    }

                    // LR5.1: writing to it is what makes it readable.
                    self.unwritten.remove(name);

                    // LR57: what was proved held for the value that was there,
                    // and the value that is there now was never checked.
                    self.forget(name);
                }
            }
            StmtKind::If {
                branches,
                otherwise,
            } => {
                // LR57: a later branch is reached only where every earlier
                // condition failed, and so is the `else`.
                let mut failed: Vec<Narrowing> = Vec::new();

                // LR5.1: a binding is written to after the `if` only where
                // every way through it wrote to the binding, so each way is
                // walked from the same starting point and the results merge.
                let before = self.unwritten.clone();
                let mut ways: Vec<HashSet<String>> = Vec::new();

                for branch in branches {
                    self.narrow(&failed, false);
                    self.condition(&branch.condition);
                    let facts = self.facts(&branch.condition);

                    self.unwritten = before.clone();
                    self.narrow(&facts, true);
                    self.block(&branch.body);
                    self.widen();
                    ways.push(self.unwritten.clone());

                    self.widen();
                    failed.extend(facts);
                }

                // Falling past every condition is a way through too, and it
                // writes to nothing unless there is an `else`.
                self.unwritten = before;
                if let Some(otherwise) = otherwise {
                    self.narrow(&failed, false);
                    self.block(otherwise);
                    self.widen();
                }
                ways.push(self.unwritten.clone());

                self.unwritten = ways.into_iter().reduce(union).unwrap_or_default();
            }
            StmtKind::While {
                label,
                condition,
                body,
            } => {
                self.condition(condition);
                let facts = self.facts(condition);

                self.narrow(&facts, true);
                self.enter_loop(label.clone(), None);
                self.block(body);
                self.loops.pop();
                self.widen();
            }
            StmtKind::Repeat { label, body, until } => {
                // `until` reads the body's bindings, so it is checked inside
                // the body's scope (LR10.3).
                let outer_unwritten = self.unwritten.clone();
                self.push();
                let repeat_scope = self.values.len() - 1;
                self.enter_loop(label.clone(), Some(repeat_scope));
                for stmt in &body.stmts {
                    self.stmt(stmt);
                }

                let flow = self.loops.pop().expect("the repeat loop is open");
                let locals: HashSet<String> = self.values[repeat_scope].keys().cloned().collect();
                for continued in flow.continues {
                    let mut path = continued.unwritten;
                    path.extend(locals.difference(&continued.declared).cloned());
                    self.unwritten = union(self.unwritten.clone(), path);
                }

                self.condition(until);
                self.unwritten
                    .retain(|name| !locals.contains(name) || outer_unwritten.contains(name));
                self.pop();
            }
            StmtKind::For {
                label,
                bindings,
                iterable,
                body,
            } => {
                // LR10.4: a range written in place yields its bounds' type.
                // LR10.5: a collection yields what it holds. Anything else
                // yields what the iterator protocol says (LR35).
                let yielded = match &iterable.kind {
                    ExprKind::Range {
                        start: Some(start),
                        end: Some(end),
                        ..
                    } => Some(vec![self.range_element(start, end)]),
                    // LR10.4: `reversed()` on a range written in place yields
                    // the same values.
                    ExprKind::Call {
                        callee,
                        method: Some(method),
                        type_args,
                        args,
                    } if method == "reversed"
                        && type_args.is_empty()
                        && args.is_empty()
                        && matches!(
                            callee.kind,
                            ExprKind::Range {
                                start: Some(_),
                                end: Some(_),
                                ..
                            }
                        ) =>
                    {
                        let ExprKind::Range {
                            start: Some(start),
                            end: Some(end),
                            ..
                        } = &callee.kind
                        else {
                            unreachable!()
                        };
                        Some(vec![self.range_element(start, end)])
                    }
                    // LR10.5: `enumerated()` written in place yields each
                    // index and the element at it.
                    ExprKind::Call {
                        callee,
                        method: Some(method),
                        type_args,
                        args,
                    } if method == "enumerated" && type_args.is_empty() && args.is_empty() => {
                        let receiver = self.expr(callee);
                        match settle(receiver.clone()) {
                            Type::Builtin {
                                kind: Builtin::List | Builtin::FrozenList,
                                args,
                            } => Some(vec![
                                Type::Primitive(Primitive::I64),
                                args.first().cloned().unwrap_or(Type::Unresolved),
                            ]),
                            _ => {
                                self.call(
                                    callee,
                                    Some(method),
                                    &receiver,
                                    &[],
                                    args,
                                    iterable.span,
                                );
                                None
                            }
                        }
                    }
                    _ => match settle(self.expr(iterable)) {
                        Type::Builtin {
                            kind:
                                Builtin::List | Builtin::FrozenList | Builtin::Set | Builtin::FrozenSet,
                            args,
                        } => Some(vec![args.first().cloned().unwrap_or(Type::Unresolved)]),
                        Type::Builtin {
                            kind: Builtin::Map | Builtin::FrozenMap,
                            args,
                        } => Some(vec![
                            args.first().cloned().unwrap_or(Type::Unresolved),
                            args.get(1).cloned().unwrap_or(Type::Unresolved),
                        ]),
                        receiver => self.iteration_yield(iterable, &receiver),
                    },
                };
                let yielded = match yielded {
                    Some(yielded) if yielded.len() == bindings.len() => yielded,
                    Some(yielded) => {
                        self.diagnostics.push(
                            Diagnostic::error(
                                codes::ITERATION_BINDINGS,
                                stmt.span,
                                format!(
                                    "this loop yields {} value{} but names {} binding{}",
                                    yielded.len(),
                                    if yielded.len() == 1 { "" } else { "s" },
                                    bindings.len(),
                                    if bindings.len() == 1 { "" } else { "s" },
                                ),
                            )
                            .note("A `for` names one binding for each value an iteration yields (LR10.5)."),
                        );
                        vec![Type::Unresolved; bindings.len()]
                    }
                    None => vec![Type::Unresolved; bindings.len()],
                };
                self.facts.record_binding(
                    stmt.span,
                    yielded.first().cloned().unwrap_or(Type::Unresolved),
                );
                self.push();
                for (binding, held) in bindings.iter().zip(yielded) {
                    self.declare(binding, held, stmt.span);
                }
                self.enter_loop(label.clone(), None);
                self.block(body);
                self.loops.pop();
                self.pop();
            }
            StmtKind::Conditional {
                branches,
                otherwise,
            } => {
                // LR48 conditions test the target, not values in scope.
                for (_, body) in branches {
                    self.block(body);
                }
                if let Some(otherwise) = otherwise {
                    self.block(otherwise);
                }
            }
            StmtKind::Unsafe(body) => {
                self.unsafely += 1;
                self.block(body);
                self.unsafely -= 1;
            }
            // LR26: a deferred call is checked where it is written, because
            // that is the scope whose names it reads.
            StmtKind::Defer(deferred) => {
                self.expr(deferred);
            }
            StmtKind::Match { scrutinee, arms } => {
                let held = self.expr(scrutinee);
                for arm in arms {
                    self.arm(arm);
                }
                self.exhaustive(&held, arms, scrutinee.span);
            }
            StmtKind::Return(value) => {
                // LR9.1: a bare `return` leaves nothing behind.
                let held = match value {
                    Some(value) => match self.returns.last().cloned().flatten() {
                        Some(wanted) => self.expr_wanting(value, &wanted),
                        None => self.expr(value),
                    },
                    None => Type::Tuple(Vec::new()),
                };

                // LR7: where no result was written down, what the body returns
                // is what it is worked out from.
                if let Some(Some(owner)) = self.bodies.last() {
                    self.collected.entry(*owner).or_default().push(held.clone());
                }

                if let Some(wanted) = self.returns.last().cloned().flatten() {
                    let span = value.as_ref().map_or(stmt.span, |value| value.span);
                    self.expect_return(&wanted, &held, span);
                }
            }
            StmtKind::Throw(value) => {
                self.expr(value);
            }
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                self.block(body);
                for clause in catches {
                    // LR25.3, LR6.3: a clause with no type catches every
                    // thrown value, which is only readable once checked.
                    let caught = clause.ty.as_ref().map_or_else(
                        || Type::Primitive(Primitive::Unknown),
                        |ty| self.resolve(ty),
                    );
                    self.facts.record_type(clause.span, caught.clone());
                    self.push();
                    self.bind(&clause.name, caught);
                    self.block(&clause.body);
                    self.pop();
                }
                if let Some(finally) = finally {
                    self.block(finally);
                }
            }
            StmtKind::Expr(expr) => {
                self.expr(expr);
            }
            StmtKind::Continue(label) => self.record_continue(label.as_deref()),
            StmtKind::Break(_) | StmtKind::Error => {}
        }
    }

    /// LR35: a `for` calls `iterator` once, then takes each item from `next`.
    fn iteration_yield(&mut self, iterable: &Expr, receiver: &Type) -> Option<Vec<Type>> {
        let (iterator_span, next_span) = crate::facts::iteration_spans(iterable.span);
        let iterator = settle(self.call(
            iterable,
            Some("iterator"),
            receiver,
            &[],
            &[],
            iterator_span,
        ));
        self.facts.record_type(iterator_span, iterator.clone());
        if matches!(iterator, Type::Unresolved) {
            return None;
        }

        let yielded = settle(self.call(iterable, Some("next"), &iterator, &[], &[], next_span));
        self.facts.record_type(next_span, yielded.clone());
        match yielded {
            Type::Optional(item) => match *item {
                Type::Tuple(items) => Some(items),
                item => Some(vec![item]),
            },
            Type::Unresolved => None,
            other => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::ITERATOR_RESULT,
                        next_span,
                        format!("`next` returns `{other}`, not an optional item"),
                    )
                    .note("`Iterator.next` returns `T?`, with `nil` ending iteration (LR35)."),
                );
                None
            }
        }
    }

    fn enter_loop(&mut self, label: Option<String>, repeat_scope: Option<usize>) {
        self.loops.push(LoopFlow {
            label,
            body_depth: self.bodies.len(),
            repeat_scope,
            continues: Vec::new(),
        });
    }

    /// LR10.3: a `continue` targeting `repeat` reaches its condition with the
    /// initialization state at the jump.
    fn record_continue(&mut self, label: Option<&str>) {
        let depth = self.bodies.len();
        let target = self.loops.iter().rposition(|flow| {
            flow.body_depth == depth
                && label.is_none_or(|label| flow.label.as_deref() == Some(label))
        });
        let Some(target) = target else { return };
        let Some(scope) = self.loops[target].repeat_scope else {
            return;
        };

        let declared = self.values[scope].keys().cloned().collect();
        self.loops[target].continues.push(ContinueFlow {
            unwritten: self.unwritten.clone(),
            declared,
        });
    }
}

pub(super) fn assigned_items(items: &[Item]) -> HashSet<String> {
    let mut names = HashSet::new();
    for item in items {
        match item {
            Item::Stmt(stmt) => assigned_stmt(stmt, &mut names),
            Item::Conditional(conditional) => {
                for (_, items) in &conditional.branches {
                    names.extend(assigned_items(items));
                }
                if let Some(items) = &conditional.otherwise {
                    names.extend(assigned_items(items));
                }
            }
            _ => {}
        }
    }
    names
}

pub(super) fn assigned_function(body: &FunctionBody) -> HashSet<String> {
    match body {
        FunctionBody::Block(block) => assigned(block),
        FunctionBody::Expr(_) => HashSet::new(),
    }
}

pub(super) fn assigned(block: &Block) -> HashSet<String> {
    let mut names = HashSet::new();
    for stmt in &block.stmts {
        assigned_stmt(stmt, &mut names);
    }
    names
}

fn assigned_stmt(stmt: &Stmt, names: &mut HashSet<String>) {
    match &stmt.kind {
        StmtKind::Assign { target, .. } => {
            if let ExprKind::Name(name) = &target.kind {
                names.insert(name.clone());
            }
        }
        StmtKind::If {
            branches,
            otherwise,
        } => {
            for branch in branches {
                names.extend(assigned(&branch.body));
            }
            if let Some(otherwise) = otherwise {
                names.extend(assigned(otherwise));
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::Repeat { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Unsafe(body) => names.extend(assigned(body)),
        StmtKind::Match { arms, .. } => {
            for arm in arms {
                if let ArmBody::Block(body) = &arm.body {
                    names.extend(assigned(body));
                }
            }
        }
        StmtKind::Conditional {
            branches,
            otherwise,
        } => {
            for (_, body) in branches {
                names.extend(assigned(body));
            }
            if let Some(otherwise) = otherwise {
                names.extend(assigned(otherwise));
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            names.extend(assigned(body));
            for clause in catches {
                names.extend(assigned(&clause.body));
            }
            if let Some(finally) = finally {
                names.extend(assigned(finally));
            }
        }
        _ => {}
    }
}
