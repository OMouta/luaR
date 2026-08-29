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
            Iterator { next_span: Span },
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
                let held = self.function.type_of(receiver).clone();
                if let Ty::Builtin { kind, args } = held
                    && matches!(
                        kind,
                        Builtin::RangeExclusive
                            | Builtin::RangeInclusive
                            | Builtin::ReversedRangeExclusive
                            | Builtin::ReversedRangeInclusive
                    )
                {
                    let element = args.first().cloned().unwrap_or(Ty::Never);
                    let start = self.emit(
                        InstKind::GetElement {
                            tuple: receiver,
                            index: 0,
                        },
                        element.clone(),
                        span,
                    );
                    let end = self.emit(
                        InstKind::GetElement {
                            tuple: receiver,
                            index: 1,
                        },
                        element.clone(),
                        span,
                    );
                    let inclusive = matches!(
                        kind,
                        Builtin::RangeInclusive | Builtin::ReversedRangeInclusive
                    );
                    let reversed = matches!(
                        kind,
                        Builtin::ReversedRangeExclusive | Builtin::ReversedRangeInclusive
                    );
                    if reversed {
                        (
                            Source::Reversed {
                                first: start,
                                inclusive,
                            },
                            self.declare(""),
                            end,
                            element,
                        )
                    } else {
                        let counter = match bindings {
                            [Binding::Name(name)] => self.declare(name),
                            _ => self.declare(""),
                        };
                        (
                            Source::Range {
                                last: end,
                                inclusive,
                            },
                            counter,
                            start,
                            element,
                        )
                    }
                } else {
                    let source = match self.function.type_of(receiver) {
                        Ty::Builtin {
                            kind: Builtin::List | Builtin::FrozenList,
                            ..
                        } => Source::List { receiver, indexed },
                        Ty::Builtin {
                            kind:
                                Builtin::Map | Builtin::FrozenMap | Builtin::Set | Builtin::FrozenSet,
                            ..
                        } => Source::Table(receiver),
                        _ => {
                            let (iterator_span, next_span) =
                                luar_sema::facts::iteration_spans(iterable.span);
                            let receiver_var = self.declare("\0iterable");
                            self.defs.insert(receiver_var, receiver);
                            let receiver =
                                Expr::new(ExprKind::Name("\0iterable".to_owned()), iterator_span);
                            let iterator =
                                self.call(&receiver, Some("iterator"), &[], iterator_span);
                            let iterator_var = self.declare("\0iterator");
                            self.defs.insert(iterator_var, iterator);
                            Source::Iterator { next_span }
                        }
                    };
                    let zero = self.emit(InstKind::Const(Const::Int(0)), Ty::INT, span);
                    (source, self.declare(""), zero, Ty::INT)
                }
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
        let mut iterated = None;
        let condition = match source {
            Source::Range { last, inclusive } => {
                let op = if inclusive {
                    BinaryOp::LessEqual
                } else {
                    BinaryOp::Less
                };
                self.emit(
                    InstKind::Binary {
                        op,
                        left: current,
                        right: last,
                    },
                    Ty::Bool,
                    span,
                )
            }
            Source::Reversed { first, inclusive } => {
                let op = if inclusive {
                    BinaryOp::GreaterEqual
                } else {
                    BinaryOp::Greater
                };
                self.emit(
                    InstKind::Binary {
                        op,
                        left: current,
                        right: first,
                    },
                    Ty::Bool,
                    span,
                )
            }
            Source::List { receiver, .. } => {
                let bound = self.emit(InstKind::Length { receiver }, Ty::INT, span);
                self.emit(
                    InstKind::Binary {
                        op: BinaryOp::Less,
                        left: current,
                        right: bound,
                    },
                    Ty::Bool,
                    span,
                )
            }
            Source::Table(receiver) => {
                let bound = self.emit(InstKind::Buckets { receiver }, Ty::INT, span);
                self.emit(
                    InstKind::Binary {
                        op: BinaryOp::Less,
                        left: current,
                        right: bound,
                    },
                    Ty::Bool,
                    span,
                )
            }
            Source::Iterator { next_span } => {
                let receiver = Expr::new(ExprKind::Name("\0iterator".to_owned()), next_span);
                let next = self.call(&receiver, Some("next"), &[], next_span);
                let condition = self.emit(InstKind::IsSome { value: next }, Ty::Bool, next_span);
                iterated = Some(next);
                condition
            }
        };
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
            Source::Iterator { next_span } => {
                let next = iterated.expect("the iterator produced its next item");
                let Ty::Optional(item) = self.function.type_of(next).clone() else {
                    self.gap(next_span, "an iterator whose `next` result is not optional");
                    return;
                };
                let item = *item;
                let value = self.emit(InstKind::Unwrap { value: next }, item.clone(), next_span);
                match item {
                    Ty::Tuple(items) => {
                        for (index, (binding, ty)) in bindings.iter().zip(items).enumerate() {
                            let member = self.emit(
                                InstKind::GetField {
                                    object: value,
                                    field: index as u32,
                                },
                                ty,
                                next_span,
                            );
                            self.bind_value(binding, member, span);
                        }
                    }
                    _ => {
                        if let Some(binding) = bindings.first() {
                            self.bind_value(binding, value, span);
                        }
                    }
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
        let next = if matches!(source, Source::Iterator { .. }) {
            current
        } else {
            let one = self.emit(InstKind::Const(Const::Int(1)), element.clone(), span);
            self.emit(
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
            )
        };
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
