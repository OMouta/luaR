//! Lowering statements.

use luar_ast::{
    Argument, BinaryOp as AstBinary, Block, Branch, CatchClause, Expr, ExprKind, Stmt, StmtKind,
};
use luar_diagnostics::Span;
use luar_sema::check::protocol_of;

use crate::inst::{Const, InstKind, Target, Terminator, Trap, Value};
use crate::lower::body::expr::binary_op;
use crate::lower::body::{Arrival, Body, Cleanup, Exit, Handler, Loop};
use crate::ty::{Builtin, Ty};

impl<'a> Body<'a> {
    pub(super) fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Local { binding, ty, value } => {
                self.local(binding, ty.as_ref(), value.as_ref(), stmt.span)
            }
            StmtKind::Const {
                binding, ty, value, ..
            } => self.local(binding, ty.as_ref(), Some(value), stmt.span),
            StmtKind::Assign { target, op, value } => self.assign(target, *op, value, stmt.span),
            StmtKind::Return(value) => self.ret(value.as_ref(), stmt.span),
            StmtKind::If {
                branches,
                otherwise,
            } => self.if_stmt(branches, otherwise.as_ref()),
            StmtKind::While {
                label,
                condition,
                body,
            } => self.while_stmt(label.as_deref(), condition, body),
            StmtKind::Repeat { label, body, until } => {
                self.repeat_stmt(label.as_deref(), body, until)
            }
            StmtKind::For {
                label,
                bindings,
                iterable,
                body,
            } => self.for_stmt(label.as_deref(), bindings, iterable, body, stmt.span),
            StmtKind::Break(label) => self.leave(label.as_deref(), Exit::Break, stmt.span),
            StmtKind::Continue(label) => self.leave(label.as_deref(), Exit::Continue, stmt.span),
            StmtKind::Match { scrutinee, arms } => self.match_stmt(scrutinee, arms),
            // LR26: nothing runs here.
            StmtKind::Defer(expr) => self
                .deferred
                .last_mut()
                .expect("a scope is open")
                .push(Cleanup::Deferred(expr.clone())),
            StmtKind::Throw(value) => self.throw_stmt(value, stmt.span),
            StmtKind::Try {
                body,
                catches,
                finally,
            } => self.try_stmt(body, catches, finally.as_ref(), stmt.span),
            // LR29.2: `unsafe` is a promise the checker made the caller keep.
            StmtKind::Unsafe(block) => self.block(block),
            StmtKind::Expr(expr) => {
                self.expr(expr, None);
            }
            StmtKind::Error => {}
        }
    }

    /// LR10.1: each condition is tested in turn, and the first that holds
    /// runs its block. What every path that reaches the end agrees on carries
    /// through; what it does not becomes a parameter of the block they meet
    /// in.
    fn if_stmt(&mut self, branches: &[Branch], otherwise: Option<&Block>) {
        let join = self.function.add_block();
        let mut arrivals = Vec::new();

        for branch in branches {
            let condition = self.expr(&branch.condition, Some(&Ty::Bool));
            let then = self.function.add_block();
            let next = self.function.add_block();
            self.terminate(Terminator::Branch {
                condition,
                then: Target::to(then),
                otherwise: Target::to(next),
            });

            let saved = self.defs.clone();
            self.switch_to(then);
            self.block(&branch.body);
            if !self.left {
                arrivals.push(Arrival {
                    block: self.current,
                    defs: self.defs.clone(),
                });
            }

            self.defs = saved;
            self.switch_to(next);
        }

        if let Some(otherwise) = otherwise {
            self.block(otherwise);
        }
        if !self.left {
            arrivals.push(Arrival {
                block: self.current,
                defs: self.defs.clone(),
            });
        }

        self.join(arrivals, join);
    }

    /// LR10.1: the expression form, whose branches each produce the value
    /// the `if` is used at.
    pub(super) fn if_expr(
        &mut self,
        branches: &[(Expr, Expr)],
        otherwise: &Expr,
        span: Span,
    ) -> Value {
        let ty = self.recorded(span);
        let join = self.function.add_block();
        let mut arrivals = Vec::new();

        for (condition, value) in branches {
            let condition = self.expr(condition, Some(&Ty::Bool));
            let then = self.function.add_block();
            let next = self.function.add_block();
            self.terminate(Terminator::Branch {
                condition,
                then: Target::to(then),
                otherwise: Target::to(next),
            });

            let saved = self.defs.clone();
            self.switch_to(then);
            let value = self.expr(value, Some(&ty));
            if !self.left {
                arrivals.push((
                    Arrival {
                        block: self.current,
                        defs: self.defs.clone(),
                    },
                    Some(value),
                ));
            }

            self.defs = saved;
            self.switch_to(next);
        }

        let value = self.expr(otherwise, Some(&ty));
        if !self.left {
            arrivals.push((
                Arrival {
                    block: self.current,
                    defs: self.defs.clone(),
                },
                Some(value),
            ));
        }

        self.join_carrying(arrivals, join, Some(ty))
            .expect("a value was carried")
    }

    /// LR10.2: the condition is tested before each pass.
    fn while_stmt(&mut self, label: Option<&str>, condition: &Expr, body: &Block) {
        let carried = self.carried(body);
        let header = self.function.add_block();
        self.jump_to(header, &carried);

        self.switch_to(header);
        self.add_params(header, &carried);
        self.bind_params(header, &carried);
        let entering = self.defs.clone();

        let condition = self.expr(condition, Some(&Ty::Bool));
        let inside = self.function.add_block();
        let exit = self.function.add_block();
        let leaving: Vec<Value> = carried.iter().map(|var| self.defs[var]).collect();
        self.add_params(exit, &carried);
        self.terminate(Terminator::Branch {
            condition,
            then: Target::to(inside),
            otherwise: Target::new(exit, leaving),
        });

        self.switch_to(inside);
        self.defs = entering.clone();
        self.loops.push(Loop {
            label: label.map(ToOwned::to_owned),
            condition: None,
            again: Some(header),
            exit,
            carried: carried.clone(),
            depth: self.scopes.len(),
        });
        self.block(body);
        if !self.left {
            self.jump_to(header, &carried);
        }
        self.loops.pop();

        self.switch_to(exit);
        self.defs = entering;
        self.bind_params(exit, &carried);
    }

    /// LR10.3: the body runs before the condition is tested, so the loop runs
    /// at least once, and the condition is part of the body's scope.
    fn repeat_stmt(&mut self, label: Option<&str>, body: &Block, until: &Expr) {
        let carried = self.carried(body);
        let inside = self.function.add_block();
        self.jump_to(inside, &carried);

        let exit = self.function.add_block();
        self.add_params(inside, &carried);

        self.switch_to(inside);
        self.bind_params(inside, &carried);
        let entering = self.defs.clone();

        // LR10.3: `until` reads what the body declared, so it is lowered
        // inside the body's scope rather than in a block of its own.
        let depth = self.scopes.len();
        self.open();
        self.loops.push(Loop {
            label: label.map(ToOwned::to_owned),
            again: None,
            condition: Some((until.clone(), inside)),
            exit,
            carried: carried.clone(),
            depth,
        });
        for stmt in &body.stmts {
            if self.left {
                break;
            }
            self.stmt(stmt);
        }

        if !self.left {
            let condition = self.expr(until, Some(&Ty::Bool));
            // LR26: the scope ends here whichever way the branch goes, so what
            // it deferred runs once, before either.
            self.unwind(depth);
            let leaving: Vec<Value> = carried.iter().map(|var| self.defs[var]).collect();
            self.add_params(exit, &carried);
            self.terminate(Terminator::Branch {
                condition,
                then: Target::new(exit, leaving.clone()),
                otherwise: Target::new(inside, leaving),
            });
        } else {
            self.add_params(exit, &carried);
        }
        self.loops.pop();
        self.scopes.pop();
        self.deferred.pop();

        self.switch_to(exit);
        self.defs = entering;
        self.bind_params(exit, &carried);
    }

    /// LR25.3: `throw` does not complete. What it throws leaves every scope
    /// between here and whatever catches it.
    fn throw_stmt(&mut self, value: &Expr, span: Span) {
        let thrown = self.expr(value, Some(&Ty::Dynamic));
        self.raise(thrown, span);
    }

    /// Sends a thrown value to the innermost `try` around it, or out of the
    /// function where there is none (LR25.3).
    pub(super) fn raise(&mut self, thrown: Value, span: Span) {
        let Some(handler) = self.handlers.last().cloned() else {
            if !self.throws {
                self.gap(span, "a throw the call graph did not reach");
                return;
            }
            // LR26: leaving the function leaves every scope it has open.
            self.unwind_from(0);
            let ty = self.function.result.clone();
            let returned = self.emit(
                InstKind::MakeEnum {
                    ty: ty.clone(),
                    variant: 1,
                    payload: vec![thrown],
                },
                ty,
                span,
            );
            self.terminate(Terminator::Return(returned));
            return;
        };

        self.unwind_from(handler.frame);
        let mut args = vec![thrown];
        args.extend(handler.carried.iter().map(|var| self.defs[var]));
        self.terminate(Terminator::Jump(Target::new(handler.block, args)));
    }

    /// LR25.3: the clauses are tried in the order they are written, the first
    /// whose type the thrown value has runs, and the `finally` runs whichever
    /// way the statement is left.
    fn try_stmt(
        &mut self,
        body: &Block,
        catches: &[CatchClause],
        finally: Option<&Block>,
        span: Span,
    ) {
        let carried = self.carried(body);
        let dispatch = self.function.add_block();
        let thrown = self.function.add_block_param(dispatch, Ty::Dynamic);
        self.add_params(dispatch, &carried);
        let entering = self.defs.clone();

        // The `finally` belongs to a scope around the guarded block, so it
        // runs after the handler rather than on the way to it.
        self.open();
        if let Some(finally) = finally {
            self.deferred
                .last_mut()
                .expect("a scope is open")
                .push(Cleanup::Finally(finally.clone()));
        }

        self.handlers.push(Handler {
            block: dispatch,
            frame: self.scopes.len(),
            carried: carried.clone(),
        });
        self.block(body);
        self.handlers.pop();

        let mut arrivals = Vec::new();
        if !self.left {
            arrivals.push(Arrival {
                block: self.current,
                defs: self.defs.clone(),
            });
        }

        self.switch_to(dispatch);
        self.defs = entering;
        self.bind_params(dispatch, &carried);
        for clause in catches {
            let next = self.function.add_block();
            let caught = match &clause.ty {
                Some(_) => {
                    let ty = self.recorded(clause.span);
                    let test = self.emit(
                        InstKind::IsType {
                            value: thrown,
                            ty: ty.clone(),
                        },
                        Ty::Bool,
                        clause.span,
                    );
                    let matched = self.function.add_block();
                    self.terminate(Terminator::Branch {
                        condition: test,
                        then: Target::to(matched),
                        otherwise: Target::to(next),
                    });
                    self.switch_to(matched);
                    self.emit(InstKind::DynValue { value: thrown }, ty, clause.span)
                }
                None => thrown,
            };

            let saved = self.defs.clone();
            self.open();
            self.bind_name(&clause.name, caught, clause.span);
            for stmt in &clause.body.stmts {
                if self.left {
                    break;
                }
                self.stmt(stmt);
            }
            self.close();
            if !self.left {
                arrivals.push(Arrival {
                    block: self.current,
                    defs: self.defs.clone(),
                });
            }

            self.defs = saved;
            self.switch_to(next);
            if clause.ty.is_none() {
                // Nothing after a clause that catches everything is reachable,
                // which the parser already rejected (LR0200).
                self.terminate(Terminator::Trap(Trap::Unreachable));
            }
        }

        // LR25.3: what no clause caught keeps going, once the `finally` around
        // the handler has run.
        if !self.left {
            self.raise(thrown, span);
        }

        let done = self.function.add_block();
        self.join(arrivals, done);
        self.close();
    }

    /// LR55: an assignment evaluates its target before its value, and a
    /// compound assignment evaluates the target once.
    fn assign(&mut self, target: &Expr, op: Option<AstBinary>, value: &Expr, span: Span) {
        match &target.kind {
            ExprKind::Name(name) => {
                let Some(var) = self.lookup(name) else {
                    self.gap(span, "an assignment to a name from another scope");
                    return;
                };
                let held = self.read_var(var, target.span);
                let wanted = self.function.type_of(held).clone();
                let written = self.written_into(Some(held), &wanted, op, value, target.span, span);
                self.write_var(var, written, span);
            }

            // LR12.2, LR59: writing a field of a mutable struct.
            ExprKind::Field {
                receiver,
                name,
                optional: false,
            } => {
                let object = self.expr(receiver, None);
                let object = self.settled(object, span);
                let held = self.function.type_of(object).clone();

                // LR43: writing a property runs its setter, where it has one.
                if self.property(&held, name).is_some() {
                    self.write_property(object, &held, name, op, value, target.span, span);
                    return;
                }

                let (Some(index), Some(fields)) =
                    (self.field_index(&held, name), self.fields_of(&held))
                else {
                    self.gap(span, "an assignment to a member that is not a stored field");
                    return;
                };

                let ty = fields[index as usize].1.clone();
                let read = op.map(|_| {
                    self.emit(
                        InstKind::GetField {
                            object,
                            field: index,
                        },
                        ty.clone(),
                        span,
                    )
                });
                let written = self.written_into(read, &ty, op, value, target.span, span);
                self.emit_void(
                    InstKind::SetField {
                        object,
                        field: index,
                        value: written,
                    },
                    span,
                );
            }

            // LR37: writing an element of a container.
            ExprKind::Index {
                receiver,
                index,
                optional: false,
            } => {
                let container = self.expr(receiver, None);
                let container = self.settled(container, span);
                let held = self.function.type_of(container).clone();
                let (key, element) = match &held {
                    Ty::Builtin {
                        kind: Builtin::Map | Builtin::FrozenMap,
                        args,
                    } => (args.first().cloned(), args.get(1).cloned()),
                    Ty::Builtin {
                        kind: Builtin::List | Builtin::Slice,
                        args,
                    } => (Some(Ty::INT), args.first().cloned()),
                    Ty::Array(element, _) => (Some(Ty::INT), Some(element.as_ref().clone())),
                    _ => {
                        self.gap(
                            span,
                            "an assignment into something the compiler cannot index",
                        );
                        return;
                    }
                };
                let Some(element) = element else {
                    self.gap(span, "an assignment into a container with no element type");
                    return;
                };

                let index = self.expr(index, key.as_ref());
                let read = op.map(|_| {
                    self.emit(
                        InstKind::GetIndex {
                            receiver: container,
                            index,
                        },
                        element.clone(),
                        span,
                    )
                });
                let written = self.written_into(read, &element, op, value, target.span, span);
                self.emit_void(
                    InstKind::SetIndex {
                        receiver: container,
                        index,
                        value: written,
                    },
                    span,
                );
            }

            _ => self.gap(span, "an assignment to this target"),
        }
    }

    /// LR43: writing a property runs its setter. A compound assignment reads
    /// through the getter first, which is the same target evaluated once
    /// (LR5.4, LR55).
    #[allow(clippy::too_many_arguments)]
    fn write_property(
        &mut self,
        object: Value,
        held: &Ty,
        name: &str,
        op: Option<AstBinary>,
        value: &Expr,
        target: Span,
        span: Span,
    ) {
        let Some((get, ty)) = self.getter(held, name) else {
            self.gap(span, "a property the compiler could not read");
            return;
        };
        let Some(set) = self.property(held, name).and_then(|held| held.set) else {
            self.gap(span, "an assignment to a property with no setter");
            return;
        };

        let read = op.map(|_| {
            self.emit(
                InstKind::Call {
                    callee: get,
                    type_args: Vec::new(),
                    args: vec![object],
                },
                ty.clone(),
                span,
            )
        });
        let written = self.written_into(read, &ty, op, value, target, span);
        self.emit_void(
            InstKind::Call {
                callee: set,
                type_args: Vec::new(),
                args: vec![object, written],
            },
            span,
        );
    }

    /// What an assignment writes: the value, or what the operator makes of
    /// what the target already held and the value (LR5.4). `a += b` is
    /// `a = a:add(b)` where the operator went through a protocol, called on
    /// the one read of the target (LR36, LR55).
    fn written_into(
        &mut self,
        held: Option<Value>,
        wanted: &Ty,
        op: Option<AstBinary>,
        value: &Expr,
        target: Span,
        span: Span,
    ) -> Value {
        if let (Some(left), Some(op)) = (held, op)
            && let Some(declaration) = self.context.facts.call(target)
            && protocol_of(op).is_some()
        {
            let args = [Argument {
                name: None,
                value: value.clone(),
                span: value.span,
            }];
            return self.call_declared(declaration, Some(left), &args, target);
        }

        let right = self.stored(value, Some(wanted));
        let (Some(left), Some(op)) = (held, op) else {
            return right;
        };
        match binary_op(op) {
            Some(op) => self.emit(InstKind::Binary { op, left, right }, wanted.clone(), span),
            None => self.missing(span, "a compound assignment with this operator"),
        }
    }

    fn ret(&mut self, value: Option<&Expr>, span: Span) {
        let result = self.declared.clone();
        let value = match value {
            Some(expr) => self.stored(expr, Some(&result)),
            None => self.emit(InstKind::Const(Const::Unit), Ty::Unit, span),
        };
        // LR26: a `return` leaves every scope the function has open, so
        // everything they deferred runs, innermost first.
        self.unwind_from(0);
        let returned = self.returned(value, span);
        self.terminate(Terminator::Return(returned));
    }

    /// What `Return` gives back for a value the function returned. Where an
    /// exception can escape, that is one half of what it gives back (LR25.3).
    pub(super) fn returned(&mut self, value: Value, span: Span) -> Value {
        if !self.throws {
            return value;
        }
        let ty = self.function.result.clone();
        self.emit(
            InstKind::MakeEnum {
                ty: ty.clone(),
                variant: 0,
                payload: vec![value],
            },
            ty,
            span,
        )
    }
}
