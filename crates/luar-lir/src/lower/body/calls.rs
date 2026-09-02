//! Lowering calls and closures.

use luar_ast::{Argument, Binding, Block, Expr, ExprKind, FunctionBody, Param, Stmt, StmtKind};
use luar_diagnostics::Span;

use crate::inst::MethodId;
use crate::inst::{Allocation, BinaryOp, Const, InstKind, Target, Terminator, Value};
use crate::lower::body::{Body, Var};
use crate::lower::names;
use crate::lower::names::assigned;
use crate::lower::thrown_or;
use crate::lower::types;
use crate::program::{FuncId, Function};
use crate::ty::{Builtin, Ty};

impl<'a> Body<'a> {
    pub(super) fn call(
        &mut self,
        callee: &Expr,
        method: Option<&str>,
        args: &[Argument],
        span: Span,
    ) -> Value {
        if let Some(builtin) = self.context.facts.builtin(span) {
            return self.builtin(builtin, callee, args, span);
        }

        if let ExprKind::Field {
            receiver,
            name: variant,
            ..
        } = &callee.kind
            && let ExprKind::Name(written) = &receiver.kind
            && written == "Result"
            && self.lookup(written).is_none()
            && let Some(tag) = match variant.as_str() {
                "Ok" => Some(0),
                "Err" => Some(1),
                _ => None,
            }
        {
            let ty = self.recorded(span);
            if matches!(
                ty,
                Ty::Builtin {
                    kind: Builtin::Result,
                    ..
                }
            ) {
                return self.construct(ty, tag, args, span);
            }
        }

        // LR15.3: a variant with a payload is written like a call and builds a
        // value, so it reaches no function and the checker recorded none.
        if let ExprKind::Field {
            receiver,
            name: variant,
            ..
        } = &callee.kind
            && let ExprKind::Name(written) = &receiver.kind
            && self.lookup(written).is_none()
        {
            let ty = self.recorded(span);
            if let Some(tag) = self.variant_of(&ty, variant) {
                return self.construct(ty, tag, args, span);
            }
        }

        // LR9.2: a function value is called through the value, and reaches
        // no declaration.
        if method.is_none()
            && self.context.facts.call(span).is_none()
            && self
                .known_type(callee)
                .or_else(|| self.maybe_recorded(callee.span))
                .is_some_and(|ty| matches!(ty, Ty::Function { .. }))
        {
            return self.through(callee, args, span);
        }

        let Some(declaration) = self.context.facts.call(span) else {
            return self.missing(span, "a call the checker did not resolve");
        };

        // LR12.2: `receiver:method(x)` is `Type.method(receiver, x)` written
        // short, so the receiver is the first argument either way.
        let receiver = method.map(|_| self.expr(callee, None));
        self.call_declared(declaration, receiver, args, span)
    }

    /// A call to the declaration the checker resolved at `span`, with its
    /// receiver already evaluated where it has one.
    pub(super) fn call_declared(
        &mut self,
        declaration: Span,
        receiver: Option<Value>,
        args: &[Argument],
        span: Span,
    ) -> Value {
        if let Some(virtual_) = self.context.virtuals.get(&declaration).copied() {
            return self.dispatch(virtual_, receiver, args, span);
        }

        let Some(reached) = self.context.callees.get(&declaration) else {
            return self.missing(span, "a call to a function with no body");
        };

        // LR19: a generic call carries what fills each of the callee's type
        // parameters, which is what monomorphization substitutes.
        let declared = reached.type_params.clone();
        let type_args = if declared.is_empty() {
            Vec::new()
        } else {
            match self.type_args(span, declared.len()) {
                Some(args) => args,
                // A method of a generic type takes the type's parameters as
                // well as its own, and the checker works out only its own.
                None => return self.missing(span, "a call whose type arguments are not all known"),
            }
        };

        let id = reached.id;
        let takes_self = reached.takes_self;
        // The caller is not inside the callee's type parameters, so it passes
        // its arguments at the parameter types with those already filled in.
        let wanted: Vec<Ty> = reached
            .params
            .iter()
            .map(|param| param.ty.substitute(&declared, &type_args))
            .collect();
        let names: Vec<String> = reached
            .params
            .iter()
            .map(|param| param.name.clone())
            .collect();
        let defaults: Vec<Option<Expr>> = reached
            .params
            .iter()
            .map(|param| param.default.clone())
            .collect();
        let variadic = reached.params.iter().position(|param| param.variadic);

        let mut filled: Vec<Option<Value>> = vec![None; wanted.len()];
        let mut rest = Vec::new();
        let mut position = 0;
        for argument in args {
            let slot = match &argument.name {
                // LR9.5: a named argument names the parameter it fills.
                Some(name) => names.iter().position(|param| param == name),
                None => {
                    let slot = position;
                    position += 1;
                    variadic
                        .filter(|variadic| slot >= *variadic)
                        .or_else(|| Some(slot).filter(|slot| *slot < wanted.len()))
                }
            };
            let value = self.stored(&argument.value, slot.map(|slot| &wanted[slot]));
            if let Some(slot) = slot {
                if Some(slot) == variadic {
                    rest.push(value);
                } else {
                    filled[slot] = Some(value);
                }
            }
        }

        for (slot, default) in defaults.iter().enumerate() {
            if filled[slot].is_some() || Some(slot) == variadic {
                continue;
            }
            let Some(default) = default else {
                return self.missing(span, "a call with no argument for a parameter");
            };
            filled[slot] = Some(self.stored(default, Some(&wanted[slot])));
        }

        let mut passed: Vec<Value> = Vec::with_capacity(filled.len() + 1);
        if takes_self {
            match receiver {
                Some(receiver) => passed.push(receiver),
                None => return self.missing(span, "a method call with no receiver"),
            }
        }
        for (slot, value) in filled.into_iter().enumerate() {
            if Some(slot) == variadic {
                let element = wanted[slot].clone();
                let ty = Ty::Builtin {
                    kind: Builtin::FrozenList,
                    args: vec![element.clone()],
                };
                passed.push(self.emit(
                    InstKind::MakeList {
                        element,
                        values: std::mem::take(&mut rest),
                    },
                    ty,
                    span,
                ));
            } else {
                match value {
                    Some(value) => passed.push(value),
                    None => return self.missing(span, "a call with no argument for a parameter"),
                }
            }
        }

        let result = self.recorded(span);
        let (call_result, task) = if reached.asynchronous {
            match &result {
                Ty::Builtin {
                    kind: Builtin::Task,
                    args,
                } if args.len() == 1 => (args[0].clone(), Some(result.clone())),
                _ => return self.missing(span, "an async call without a task result"),
            }
        } else {
            (result.clone(), None)
        };
        if reached.throws {
            let produced = self.emit(
                InstKind::Call {
                    callee: id,
                    type_args,
                    args: passed,
                },
                thrown_or(call_result.clone()),
                span,
            );
            if task.is_some() {
                return self.completed_task(produced, task, span);
            }
            let produced = self.caught_or_raised(produced, call_result, span);
            return produced;
        }

        let produced = self.emit(
            InstKind::Call {
                callee: id,
                type_args,
                args: passed,
            },
            call_result.clone(),
            span,
        );
        let produced = match task {
            Some(_) => self.completed_result(produced, call_result, span),
            None => produced,
        };
        self.completed_task(produced, task, span)
    }

    /// LR25.3: a call that may have thrown says which happened, so the caller
    /// reads what it returned on one path and sends what it threw on outward
    /// on the other.
    pub(super) fn caught_or_raised(&mut self, produced: Value, result: Ty, span: Span) -> Value {
        let tag = self.emit(InstKind::GetTag { value: produced }, Ty::INT, span);
        let threw = self.emit(InstKind::Const(Const::Int(1)), Ty::INT, span);
        let raised = self.emit(
            InstKind::Binary {
                op: BinaryOp::Equal,
                left: tag,
                right: threw,
            },
            Ty::Bool,
            span,
        );

        let unwinding = self.function.add_block();
        let returned = self.function.add_block();
        self.terminate(Terminator::Branch {
            condition: raised,
            then: Target::to(unwinding),
            otherwise: Target::to(returned),
        });

        self.switch_to(unwinding);
        let thrown = self.emit(
            InstKind::GetPayload {
                value: produced,
                variant: 1,
                field: 0,
            },
            Ty::Dynamic,
            span,
        );
        self.raise(thrown, span);

        self.switch_to(returned);
        self.emit(
            InstKind::GetPayload {
                value: produced,
                variant: 0,
                field: 0,
            },
            result,
            span,
        )
    }

    /// What fills the callee's type parameters at `span`, where the checker
    /// worked out every one of them (LR19).
    pub(super) fn type_args(&mut self, span: Span, wanted: usize) -> Option<Vec<Ty>> {
        let recorded = self.context.facts.type_args(span)?;
        if recorded.len() != wanted {
            return None;
        }
        recorded
            .iter()
            .map(|ty| types::convert(ty, self.context.ids).ok())
            .collect()
    }

    /// LR9.2, LR9.8: a closure is a function of the program, plus the values
    /// it captured from the scope it was written in.
    pub(super) fn closure(
        &mut self,
        asynchronous: bool,
        params: &[Param],
        body: &FunctionBody,
        span: Span,
    ) -> Value {
        let ty = self.recorded(span);
        let Ty::Function {
            asynchronous: recorded,
            params: takes,
            result,
        } = ty.clone()
        else {
            return self.missing(span, "a closure whose type the checker did not work out");
        };
        if recorded != asynchronous {
            return self.missing(span, "a closure whose async type does not match its body");
        }
        if takes.len() != params.len() {
            return self.missing(span, "a closure of a shape the checker did not agree on");
        }
        let written = match body {
            FunctionBody::Block(block) => block.clone(),
            // An arrow closure is one expression, and returning it is what it
            // does (LR9.2).
            FunctionBody::Expr(value) => Block {
                stmts: vec![Stmt::new(StmtKind::Return(Some(value.clone())), value.span)],
                span: value.span,
            },
        };

        let Some(captures) = self.captures(&written, span) else {
            return self.missing(span, "a closure capturing a binding something assigns to");
        };
        if captures.iter().any(|(_, var)| self.slots.contains_key(var)) {
            return self.missing(span, "a closure capturing a binding whose address is taken");
        }

        let captured: Vec<(String, Ty)> = captures
            .iter()
            .map(|(name, var)| (name.clone(), self.function.type_of(self.defs[var]).clone()))
            .collect();
        let mut bindings: Vec<Binding> = Vec::with_capacity(params.len());
        let mut taken: Vec<Ty> = vec![ty.clone()];
        for (param, ty) in params.iter().zip(takes) {
            bindings.push(param.binding.clone());
            taken.push(ty);
        }

        let id = FuncId(self.context.next_function.get());
        self.context.next_function.set(id.0 + 1);

        let mut shell = Function::new(
            format!("{}#{}", self.function.name, id.0),
            taken,
            thrown_or(*result),
            span,
        );
        shell.asynchronous = asynchronous;
        let (built, made, gaps) =
            Body::new(self.context, shell, true).lower(Some(&captured), &bindings, &written);
        self.made.push((id, built));
        self.made.extend(made);
        self.gaps.extend(gaps);

        let held = captures.iter().map(|(_, var)| self.defs[var]).collect();
        self.emit(
            InstKind::MakeClosure {
                func: id,
                captures: held,
            },
            ty,
            span,
        )
    }

    /// The bindings a closure body reaches out of its own scope for, in the
    /// order it names them.
    fn captures(&mut self, body: &Block, span: Span) -> Option<Vec<(String, Var)>> {
        let _ = span;
        let mut inside = Vec::new();
        assigned(body, &mut inside);

        let mut named = Vec::new();
        names::in_block(body, &mut named);

        let mut captures: Vec<(String, Var)> = Vec::new();
        for name in named {
            let Some(var) = self.lookup(&name) else {
                continue;
            };
            if !self.defs.contains_key(&var) || captures.iter().any(|(_, held)| *held == var) {
                continue;
            }
            // LR9.8: one something assigns to is captured as its cell.
            if !self.cells.contains(&var)
                && (self.mutated.contains(&name) || inside.contains(&name))
            {
                return None;
            }
            captures.push((name, var));
        }
        Some(captures)
    }

    /// LR9.2: a call through a value calls whatever it holds, which is a
    /// closure or a function passed as one.
    fn through(&mut self, callee: &Expr, args: &[Argument], span: Span) -> Value {
        let value = self.expr(callee, None);
        let Ty::Function {
            asynchronous,
            params,
            result,
        } = self.function.type_of(value).clone()
        else {
            return self.missing(span, "a call through something that is not a function");
        };
        if args.len() != params.len() || args.iter().any(|argument| argument.name.is_some()) {
            return self.missing(span, "a call through a value that does not line up");
        }

        let passed = args
            .iter()
            .zip(&params)
            .map(|(argument, ty)| self.stored(&argument.value, Some(ty)))
            .collect();
        // LR9.3: what a call through a function value gives back is what the
        // function type says, which is more than the checker settles today.
        let held = self.maybe_recorded(span).unwrap_or_else(|| {
            if asynchronous {
                Ty::Builtin {
                    kind: Builtin::Task,
                    args: vec![result.as_ref().clone()],
                }
            } else {
                result.as_ref().clone()
            }
        });
        let (call_result, task) = if asynchronous {
            match &held {
                Ty::Builtin {
                    kind: Builtin::Task,
                    args,
                } if args.len() == 1 => (args[0].clone(), Some(held.clone())),
                _ => return self.missing(span, "an async call without a task result"),
            }
        } else {
            (held.clone(), None)
        };
        let produced = self.emit(
            InstKind::CallIndirect {
                callee: value,
                args: passed,
            },
            thrown_or(call_result.clone()),
            span,
        );
        if task.is_some() {
            return self.completed_task(produced, task, span);
        }
        self.caught_or_raised(produced, call_result, span)
    }

    /// LR18.1: a call through an interface finds its implementation at
    /// runtime, until devirtualization proves there is only one.
    fn dispatch(
        &mut self,
        method: MethodId,
        receiver: Option<Value>,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let Some(receiver) = receiver else {
            return self.missing(span, "an interface call with no receiver");
        };
        if args.iter().any(|argument| argument.name.is_some()) {
            return self.missing(span, "an interface call with named arguments");
        }

        let passed: Vec<Value> = args
            .iter()
            .map(|argument| self.stored(&argument.value, None))
            .collect();
        let result = self.recorded(span);
        let (throws, asynchronous) = match &self.context.program.nominal(method.interface).shape {
            crate::program::Shape::Interface(interface) => interface
                .methods
                .get(method.slot as usize)
                .map_or((false, false), |method| {
                    (method.throws, method.asynchronous)
                }),
            _ => (false, false),
        };
        let (call_result, task) = if asynchronous {
            match &result {
                Ty::Builtin {
                    kind: Builtin::Task,
                    args,
                } if args.len() == 1 => (args[0].clone(), Some(result.clone())),
                _ => return self.missing(span, "an async call without a task result"),
            }
        } else {
            (result.clone(), None)
        };
        if !throws {
            let produced = self.emit(
                InstKind::CallVirtual {
                    method,
                    receiver,
                    args: passed,
                },
                call_result.clone(),
                span,
            );
            let produced = match task {
                Some(_) => self.completed_result(produced, call_result, span),
                None => produced,
            };
            return self.completed_task(produced, task, span);
        }
        let produced = self.emit(
            InstKind::CallVirtual {
                method,
                receiver,
                args: passed,
            },
            thrown_or(call_result.clone()),
            span,
        );
        if task.is_some() {
            return self.completed_task(produced, task, span);
        }
        self.caught_or_raised(produced, call_result, span)
    }

    fn completed_result(&mut self, value: Value, result: Ty, span: Span) -> Value {
        let ty = thrown_or(result);
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

    fn completed_task(&mut self, value: Value, task: Option<Ty>, span: Span) -> Value {
        match task {
            Some(task) => self.emit(
                InstKind::MakeStruct {
                    ty: task.clone(),
                    fields: vec![value],
                    allocation: Allocation::Managed,
                },
                task,
                span,
            ),
            None => value,
        }
    }
}
