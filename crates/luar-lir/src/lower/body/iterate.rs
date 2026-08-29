//! Lowering `for` loops.

use luar_ast::{Binding, Block, Expr, ExprKind};
use luar_diagnostics::Span;

use crate::inst::{BinaryOp, Const, InstKind, Target, Terminator, Value};
use crate::lower::body::{Body, Loop};
use crate::ty::{Builtin, IntTy, Ty};

impl<'a> Body<'a> {
    /// LR10.4: a `for` over a range written in place counts from its lower
    /// bound up to its upper one, and runs zero times where the lower bound
    /// is the greater. LR10.5: one over a list counts through its indices,
    /// and one over a map or a set counts through its buckets and runs the
    /// body for each that is occupied. Anything else iterates through the
    /// protocol (LR35).
    pub(super) fn for_stmt(
        &mut self,
        label: Option<&str>,
        bindings: &[Binding],
        iterable: &Expr,
        body: &Block,
        span: Span,
    ) {
        enum Source {
            Range { last: Value, inclusive: bool },
            Reversed { first: Value, inclusive: bool },
            List { receiver: Value, indexed: bool },
            Table(Value),
        }

        let carried = self.carried(body);
        let header = self.function.add_block();
        self.open();
        let (source, counter, first, element) = match (&iterable.kind, bindings) {
            (
                ExprKind::Range {
                    start: Some(start),
                    end: Some(end),
                    inclusive,
                },
                [Binding::Name(name)],
            ) => {
                let element = self
                    .declared_type(span)
                    .or_else(|| self.known_type(start))
                    .unwrap_or(Ty::Int(IntTy::I64));
                let first = self.expr(start, Some(&element));
                let last = self.expr(end, Some(&element));
                let source = Source::Range {
                    last,
                    inclusive: *inclusive,
                };
                (source, self.declare(name), first, element)
            }
            (ExprKind::Range { .. }, _) => {
                self.gap(span, "a range loop that does not bind one name");
                return;
            }
            (
                ExprKind::Call {
                    callee,
                    method: Some(method),
                    args,
                    ..
                },
                _,
            ) if method == "reversed" && args.is_empty() => {
                let ExprKind::Range {
                    start: Some(start),
                    end: Some(end),
                    inclusive,
                } = &callee.kind
                else {
                    self.gap(
                        span,
                        "`reversed()` on something other than a range written in place",
                    );
                    return;
                };
                let element = self
                    .declared_type(span)
                    .or_else(|| self.known_type(start))
                    .unwrap_or(Ty::Int(IntTy::I64));
                let first = self.expr(start, Some(&element));
                let last = self.expr(end, Some(&element));
                let source = Source::Reversed {
                    first,
                    inclusive: *inclusive,
                };
                (source, self.declare(""), last, element)
            }
            _ => {
                let (iterable, indexed) = match &iterable.kind {
                    ExprKind::Call {
                        callee,
                        method: Some(method),
                        args,
                        ..
                    } if method == "enumerated" && args.is_empty() => (callee.as_ref(), true),
                    _ => (iterable, false),
                };
                let receiver = self.expr(iterable, None);
                let source = match self.function.type_of(receiver) {
                    Ty::Builtin {
                        kind: Builtin::List | Builtin::FrozenList,
                        ..
                    } => Source::List { receiver, indexed },
                    Ty::Builtin {
                        kind: Builtin::Map | Builtin::FrozenMap | Builtin::Set | Builtin::FrozenSet,
                        ..
                    } => Source::Table(receiver),
                    _ => {
                        self.gap(
                            span,
                            "a `for` over something that is not a range or a collection",
                        );
                        return;
                    }
                };
                let zero = self.emit(InstKind::Const(Const::Int(0)), Ty::INT, span);
                (source, self.declare(""), zero, Ty::INT)
            }
        };

        self.defs.insert(counter, first);
        let mut passing = carried.clone();
        passing.push(counter);
        self.jump_to(header, &passing);

        self.switch_to(header);
        self.add_params(header, &passing);
        self.bind_params(header, &passing);
        let entering = self.defs.clone();

        let current = self.defs[&counter];
        let descending = matches!(source, Source::Reversed { .. });
        let (op, bound) = match source {
            Source::Range { last, inclusive } => {
                let op = if inclusive {
                    BinaryOp::LessEqual
                } else {
                    BinaryOp::Less
                };
                (op, last)
            }
            Source::Reversed { first, inclusive } => {
                let op = if inclusive {
                    BinaryOp::GreaterEqual
                } else {
                    BinaryOp::Greater
                };
                (op, first)
            }
            Source::List { receiver, .. } => (
                BinaryOp::Less,
                self.emit(InstKind::Length { receiver }, Ty::INT, span),
            ),
            Source::Table(receiver) => (
                BinaryOp::Less,
                self.emit(InstKind::Buckets { receiver }, Ty::INT, span),
            ),
        };
        let condition = self.emit(
            InstKind::Binary {
                op,
                left: current,
                right: bound,
            },
            Ty::Bool,
            span,
        );
        let inside = self.function.add_block();
        let step = self.function.add_block();
        let exit = self.function.add_block();
        let leaving: Vec<Value> = carried.iter().map(|held| self.defs[held]).collect();
        self.add_params(exit, &carried);
        self.add_params(step, &carried);
        self.terminate(Terminator::Branch {
            condition,
            then: Target::to(inside),
            otherwise: Target::new(exit, leaving.clone()),
        });

        self.switch_to(inside);
        self.defs = entering.clone();
        match source {
            Source::Range { .. } => {}
            Source::Reversed { inclusive, .. } => {
                let value = if inclusive {
                    current
                } else {
                    let one = self.emit(InstKind::Const(Const::Int(1)), element.clone(), span);
                    self.emit(
                        InstKind::Binary {
                            op: BinaryOp::Subtract,
                            left: current,
                            right: one,
                        },
                        element.clone(),
                        span,
                    )
                };
                if let Some(binding) = bindings.first() {
                    self.bind_value(binding, value, span);
                }
            }
            Source::List { receiver, indexed } => {
                let held = self.collection_args(receiver);
                let element = self.emit(
                    InstKind::GetIndex {
                        receiver,
                        index: current,
                    },
                    held.first().cloned().unwrap_or(Ty::Never),
                    span,
                );
                let yielded = if indexed {
                    vec![current, element]
                } else {
                    vec![element]
                };
                for (binding, value) in bindings.iter().zip(yielded) {
                    self.bind_value(binding, value, span);
                }
            }
            Source::Table(receiver) => {
                let occupied = self.emit(
                    InstKind::Occupied {
                        receiver,
                        index: current,
                    },
                    Ty::Bool,
                    span,
                );
                let found = self.function.add_block();
                self.terminate(Terminator::Branch {
                    condition: occupied,
                    then: Target::to(found),
                    otherwise: Target::new(step, leaving),
                });
                self.switch_to(found);

                let held = self.collection_args(receiver);
                let reads = [
                    InstKind::EntryKey {
                        receiver,
                        index: current,
                    },
                    InstKind::EntryValue {
                        receiver,
                        index: current,
                    },
                ];
                for ((binding, read), ty) in bindings.iter().zip(reads).zip(held) {
                    let value = self.emit(read, ty, span);
                    self.bind_value(binding, value, span);
                }
            }
        }
        self.loops.push(Loop {
            label: label.map(ToOwned::to_owned),
            again: Some(step),
            exit,
            carried: carried.clone(),
            depth: self.scopes.len(),
        });
        self.block(body);
        if !self.left {
            self.jump_to(step, &carried);
        }
        self.loops.pop();

        self.switch_to(step);
        self.defs = entering.clone();
        self.bind_params(step, &carried);
        let one = self.emit(InstKind::Const(Const::Int(1)), element.clone(), span);
        let next = self.emit(
            InstKind::Binary {
                op: if descending {
                    BinaryOp::Subtract
                } else {
                    BinaryOp::Add
                },
                left: current,
                right: one,
            },
            element,
            span,
        );
        self.defs.insert(counter, next);
        self.jump_to(header, &passing);
        self.close();

        self.switch_to(exit);
        self.defs = entering;
        self.bind_params(exit, &carried);
    }

    /// The type arguments of the collection `receiver` holds.
    pub(super) fn collection_args(&self, receiver: Value) -> Vec<Ty> {
        match self.function.type_of(receiver) {
            Ty::Builtin { args, .. } => args.clone(),
            _ => Vec::new(),
        }
    }
}
