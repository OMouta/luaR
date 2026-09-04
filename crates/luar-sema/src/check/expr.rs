//! Expressions, and the members, fields, and variants they reach.

use std::collections::{BTreeMap, HashMap, HashSet};

use luar_ast::{Expr, ExprKind, FieldInit, FunctionBody, InterpolationPart, MapKey, Visibility};
use luar_diagnostics::{Code, Diagnostic, Span, codes};

use crate::aliases::substitute;
use crate::modules::ModuleId;
use crate::names::Origin;
use crate::table::{Decl, Field, Variant};
use crate::types::{Builtin, Primitive, Type};

use super::builtins::{article, is_collection};
use super::calls::{against, filled, infer};
use super::interfaces::same_signature;
use super::narrow::Place;
use super::operators::{settle, unify};
use super::stmt::assigned_function;
use super::{Checker, ClosureCaptures, Narrowing, ThreadMarker};

impl Checker<'_> {
    /// The type of an expression, recorded for the stages after this one.
    pub(super) fn expr(&mut self, expr: &Expr) -> Type {
        let ty = self.expr_type(expr);
        self.facts.record_type(expr.span, ty.clone());
        ty
    }

    /// The type a member is read off. A bracket literal with a member read
    /// off it has nothing asking for an array, so it is a list (LR13.1).
    fn read_off(&mut self, expr: &Expr) -> Type {
        let held = self.expr(expr);
        if !matches!(held, Type::SequenceLiteral(_)) {
            return held;
        }
        let held = settle(held);
        self.facts.record_type(expr.span, held.clone());
        held
    }

    /// LR25.1: `Result.Ok(value)` and `Result.Err(error)` take the type
    /// arguments of the `Result` the value is asked for.
    pub(super) fn expr_wanting(&mut self, expr: &Expr, wanted: &Type) -> Type {
        if let ExprKind::List(items) = &expr.kind
            && let Type::Array(_, Some(length)) = wanted
            && u64::try_from(items.len()).ok() != Some(*length)
        {
            self.diagnostics.push(Diagnostic::error(
                codes::ARRAY_LENGTH,
                expr.span,
                format!(
                    "this has {} elements, and the array has {length}",
                    items.len()
                ),
            ));
        }

        // LR9.2: a closure takes the parameter types it does not write from
        // the function type asked for.
        if let ExprKind::Function { params, .. } = &expr.kind
            && let Type::Function {
                params: expected, ..
            } = wanted
            && expected.len() == params.len()
        {
            let expected = expected.clone();
            let ty = self.function_expr(expr, &expected);
            self.facts.record_type(expr.span, ty.clone());
            return ty;
        }
        if let ExprKind::Call {
            callee,
            method: None,
            type_args,
            args,
        } = &expr.kind
            && type_args.is_empty()
            && result_variant(callee).is_some()
            && !self.shadowed("Result")
            && let Type::Builtin {
                kind: Builtin::Result,
                args: written,
            } = wanted
            && written.len() == 2
        {
            let written = written.clone();
            let receiver = self.expr(callee);
            let ty = self.call(callee, None, &receiver, &written, args, expr.span);
            self.facts.record_type(expr.span, ty.clone());
            return ty;
        }
        // LR16.1, LR10.1: every case or branch is checked at the type the
        // whole expression is used at.
        match &expr.kind {
            ExprKind::Match { scrutinee, arms } => {
                let ty = self.match_expr(scrutinee, arms, Some(wanted));
                self.facts.record_type(expr.span, ty.clone());
                return ty;
            }
            ExprKind::If {
                branches,
                otherwise,
            } => {
                let ty = self.if_expr(branches, otherwise, Some(wanted));
                self.facts.record_type(expr.span, ty.clone());
                return ty;
            }
            _ => {}
        }
        // LR19: a type argument nothing passes is read from the type the
        // result is used at.
        let contextual = match &expr.kind {
            ExprKind::Call { .. } => true,
            ExprKind::Record { path, .. } => !path.is_empty(),
            ExprKind::Range { .. } => true,
            _ => false,
        };
        if contextual {
            self.expected = Some(wanted.clone());
            let ty = self.expr(expr);
            self.expected = None;
            return ty;
        }
        self.expr(expr)
    }

    /// LR9.2: a closure, with a parameter type it does not write taken from
    /// `expected`, and the result of an arrow closure worked out from its
    /// expression (LR7).
    fn function_expr(&mut self, expr: &Expr, expected: &[Type]) -> Type {
        let ExprKind::Function {
            asynchronous,
            params,
            result,
            body,
        } = &expr.kind
        else {
            return Type::Unresolved;
        };
        let base = self.values.len();
        let outer_mutations = self.mutations.last().cloned().unwrap_or_default();
        self.push();
        self.closures.push(ClosureCaptures {
            base,
            values: HashMap::new(),
            mutable: HashSet::new(),
            outer_mutations,
        });
        self.mutations.push(assigned_function(body));
        let mut types = Vec::with_capacity(params.len());
        for (i, param) in params.iter().enumerate() {
            let declared = match &param.ty {
                Some(ty) => self.resolve(ty),
                None => expected.get(i).cloned().unwrap_or(Type::Unresolved),
            };
            self.param(param, declared.clone());
            types.push(declared);
        }

        let declared = result.as_ref().map(|result| self.resolve(result));

        self.returns.push(declared.clone());
        self.asynchronously.push(*asynchronous);
        // LR7: a block body with no written result is worked out from what
        // it returns, collected under the closure's own span.
        self.bodies.push(declared.is_none().then_some(expr.span));

        let produced = match body.as_ref() {
            FunctionBody::Block(block) => {
                for stmt in &block.stmts {
                    self.stmt(stmt);
                }
                self.collected
                    .remove(&expr.span)
                    .unwrap_or_default()
                    .into_iter()
                    .map(settle)
                    .reduce(unify)
                    .or_else(|| Some(Type::Tuple(Vec::new())))
            }
            FunctionBody::Expr(expr) => Some(self.expr(expr)),
        };

        self.mutations.pop();
        let captures = self.closures.pop().expect("a closure is open");
        self.bodies.pop();
        self.asynchronously.pop();
        self.returns.pop();
        self.pop();

        let sendable = captures.values.iter().all(|(name, ty)| {
            !captures.mutable.contains(name)
                && !captures.outer_mutations.contains(name)
                && self.has_thread_marker(ty, ThreadMarker::Send)
        });
        let returns = declared
            .or_else(|| produced.map(settle))
            .unwrap_or(Type::Unresolved);

        Type::Function {
            asynchronous: *asynchronous,
            sendable,
            params: types,
            result: Box::new(returns),
        }
    }

    /// An expression checked at `wanted` where there is one (LR19, LR25.1).
    pub(super) fn expr_maybe_wanting(&mut self, expr: &Expr, wanted: Option<&Type>) -> Type {
        match wanted {
            Some(wanted) => self.expr_wanting(expr, wanted),
            None => self.expr(expr),
        }
    }

    /// LR16.1: a `match` expression produces what its cases produce, which
    /// is one type, or the type the expression is used at.
    pub(super) fn match_expr(
        &mut self,
        scrutinee: &Expr,
        arms: &[luar_ast::MatchArm],
        wanted: Option<&Type>,
    ) -> Type {
        let held = self.expr(scrutinee);
        let (rows, produced) = self.arms(arms, &held, scrutinee, wanted);
        self.exhaustive(&held, &rows, scrutinee.span);
        produced.unwrap_or(Type::Unresolved)
    }

    /// LR10.1: an `if` expression produces what its branches produce, which
    /// is one type, or the type the expression is used at. Each branch is
    /// checked knowing what its condition proved (LR57).
    pub(super) fn if_expr(
        &mut self,
        branches: &[(Expr, Expr)],
        otherwise: &Expr,
        wanted: Option<&Type>,
    ) -> Type {
        let mut produced = wanted.cloned();
        let mut failed: Vec<Narrowing> = Vec::new();

        for (condition, value) in branches {
            self.narrow(&failed, false);
            self.condition(condition);
            let facts = self.facts(condition);

            self.narrow(&facts, true);
            let held = self.expr_maybe_wanting(value, produced.as_ref());
            self.widen();
            self.widen();

            produced = Some(self.agree(produced, held, value.span, codes::IF_BRANCH_TYPE));
            failed.extend(facts);
        }

        self.narrow(&failed, false);
        let held = self.expr_maybe_wanting(otherwise, produced.as_ref());
        self.widen();
        produced = Some(self.agree(produced, held, otherwise.span, codes::IF_BRANCH_TYPE));

        produced.unwrap_or(Type::Unresolved)
    }

    /// The type two branches of one expression agree on, reporting `code` at
    /// `span` where they do not (LR10.1, LR16.1).
    pub(super) fn agree(
        &mut self,
        running: Option<Type>,
        held: Type,
        span: Span,
        code: Code,
    ) -> Type {
        let Some(running) = running else {
            return held;
        };
        if matches!(running, Type::Unresolved) || matches!(held, Type::Unresolved) {
            return Type::Unresolved;
        }

        let unified = unify(running.clone(), held.clone());
        if !matches!(unified, Type::Unresolved) {
            return unified;
        }
        if self.accepts(&running, &held) {
            return running;
        }
        if self.accepts(&held, &running) {
            return held;
        }

        self.diagnostics.push(
            Diagnostic::error(
                code,
                span,
                format!(
                    "this produces {}, and the branches before it produce `{running}`",
                    article(&held)
                ),
            )
            .note("Every branch of one expression produces a compatible type (LR10.1, LR16.1)."),
        );
        running
    }

    fn expr_type(&mut self, expr: &Expr) -> Type {
        match &expr.kind {
            ExprKind::Nil => Type::Primitive(Primitive::Nil),
            ExprKind::Bool(_) => Type::BOOL,
            ExprKind::Integer(value) => Type::IntegerLiteral(*value),
            ExprKind::Float(_) => Type::FloatLiteral,
            ExprKind::String(_) => Type::STRING,
            ExprKind::ByteString(_) => Type::Primitive(Primitive::Bytes),
            ExprKind::Char(_) => Type::Primitive(Primitive::Char),
            ExprKind::Interpolation(parts) => {
                for part in parts {
                    if let InterpolationPart::Expr(expr) = part {
                        self.expr(expr);
                    }
                }
                Type::STRING
            }
            ExprKind::Name(name) => {
                // LR5.1: the compiler proves a binding was written to before
                // it is read, and this is where it fails to.
                if self.unwritten.contains(name) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::UNINITIALIZED_READ,
                            expr.span,
                            format!("`{name}` is read before anything writes to it"),
                        )
                        .note("A binding declared without a value holds nothing yet (LR5.1)."),
                    );
                    self.unwritten.remove(name);
                }

                let held = self.name(name);
                // LR21.1, LR24: a module-level `const` read from outside the
                // function's own bindings, imported or written further down.
                if matches!(held, Type::Unresolved)
                    && let Some((module, declared, ty)) = self.module_constant(name)
                {
                    self.facts.record_constant(expr.span, module, declared);
                    return ty;
                }
                // LR23.1: a compile-time function is gone by the time a body
                // is checked, so a read of its name reaches nothing.
                if matches!(held, Type::Unresolved) && self.compile_time_function(name) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::COMPILE_TIME_FUNCTION,
                            expr.span,
                            format!("`{name}` exists only while a decorator runs"),
                        )
                        .note("A function over decorator metadata has no runtime value (LR23.1)."),
                    );
                }
                held
            }
            ExprKind::Unary { op, operand } => self.unary(*op, operand),
            ExprKind::Binary {
                op,
                op_span,
                left,
                right,
            } => self.binary(*op, *op_span, left, right),
            ExprKind::Range {
                start,
                end,
                inclusive,
            } => {
                let element = match (start.as_deref(), end.as_deref()) {
                    (Some(start), Some(end)) => self.range_element(start, end),
                    (Some(bound), None) | (None, Some(bound)) => settle(self.expr(bound)),
                    (None, None) => self
                        .expected
                        .as_ref()
                        .and_then(|expected| match expected {
                            Type::Builtin { args, .. } => args.first().cloned(),
                            Type::Union(members) => {
                                members.iter().find_map(|member| match member {
                                    Type::Builtin { args, .. } => args.first().cloned(),
                                    _ => None,
                                })
                            }
                            _ => None,
                        })
                        .unwrap_or(Type::Unresolved),
                };
                Type::Builtin {
                    kind: if *inclusive {
                        Builtin::RangeInclusive
                    } else {
                        Builtin::RangeExclusive
                    },
                    args: vec![element],
                }
            }
            ExprKind::Call {
                callee,
                method,
                type_args,
                args,
            } => {
                let written: Vec<Type> = type_args.iter().map(|ty| self.resolve(ty)).collect();
                // The callee is an expression of its own, and what the call
                // is used at says nothing about it.
                let expected = self.expected.take();
                let receiver = self.read_off(callee);
                self.expected = expected;
                let produced = self.call(
                    callee,
                    method.as_deref(),
                    &receiver,
                    &written,
                    args,
                    expr.span,
                );
                // LR57: what was called may have written through another
                // holder of any object in scope.
                self.forget_nested();
                produced
            }
            ExprKind::Field {
                receiver,
                name,
                optional,
            } => {
                // LR15.3: a variant is reached through its enum, which is a
                // type and not a value, so this builds rather than reads.
                if let ExprKind::Name(owner) = &receiver.kind
                    && let Some((built, Variant::Unit)) = self.variant(owner, name)
                {
                    return built;
                }

                let held = self.read_off(receiver);

                // LR57: what a condition proved about this field wins over
                // what it is declared as, for as long as the branch lasts.
                if !*optional && let Some(proved) = self.proved_at(expr) {
                    return proved;
                }

                // LR8: `?.` is what reaches through an optional, so it reads
                // the member off what the optional holds.
                if *optional {
                    let member = self.member(&held.without_nil(), name, expr.span);
                    // The chain gives nothing where the receiver is absent.
                    member.optional()
                } else {
                    self.member(&held, name, expr.span)
                }
            }
            ExprKind::Index {
                receiver,
                index,
                optional,
            } => {
                let held = self.read_off(receiver);
                let key = if matches!(
                    held,
                    Type::Builtin {
                        kind: Builtin::List | Builtin::Slice,
                        ..
                    }
                ) && let ExprKind::Range { inclusive, .. } = &index.kind
                {
                    let range = Type::Builtin {
                        kind: if *inclusive {
                            Builtin::RangeInclusive
                        } else {
                            Builtin::RangeExclusive
                        },
                        args: vec![Type::Primitive(Primitive::I64)],
                    };
                    self.expr_wanting(index, &range)
                } else {
                    self.expr(index)
                };

                // LR57: what a condition proved about this element wins over
                // what the container gives back.
                if !*optional && let Some(proved) = self.proved_at(expr) {
                    return proved;
                }

                // LR8: `?[` reaches through an optional the way `?.` does.
                let container = if *optional { held.without_nil() } else { held };

                let element = self.indexed(&container, &key, index.span, expr.span);
                if *optional {
                    element.optional()
                } else {
                    element
                }
            }
            ExprKind::Try(inner) => {
                let held = self.expr(inner);
                self.propagated(&held, expr.span)
            }
            ExprKind::Await(inner) => {
                let held = self.expr(inner);
                // LR27.2, LR57: another task runs while this one waits.
                self.forget_nested();
                self.awaited(&held, expr.span)
            }
            ExprKind::Cast { value, ty } => {
                let held = self.expr(value);
                let wanted = self.resolve(ty);
                self.convertible(&held, &wanted, expr.span);
                wanted
            }
            ExprKind::TypeTest { value, ty } => {
                self.expr(value);
                let tested = self.resolve(ty);
                self.facts.record_type(ty.span, tested);
                Type::BOOL
            }
            ExprKind::AddressOf { mutable, operand } => {
                let target = self.expr(operand);
                self.address_of(*mutable, operand, expr.span);
                Type::Pointer {
                    mutable: *mutable,
                    target: Box::new(target),
                }
            }
            ExprKind::Tuple(items) => {
                let members = items.iter().map(|item| settle(self.expr(item))).collect();
                Type::Tuple(members)
            }
            // LR13.1, LR71: a bracket literal is a sequence, and which one it
            // fills comes from context, so it stays a literal until asked.
            ExprKind::List(items) => {
                let mut element = Type::Unresolved;
                for (i, item) in items.iter().enumerate() {
                    let held = self.expr(item);
                    element = if i == 0 { held } else { unify(element, held) };
                }
                Type::SequenceLiteral(Box::new(element))
            }
            ExprKind::Record { path, fields } => {
                // The values keep their literal types, because what a field
                // declares is the context that settles them (LR39).
                let values: Vec<Type> =
                    fields.iter().map(|field| self.expr(&field.value)).collect();

                // LR12.2: a path names the type being built.
                if path.is_empty() {
                    Type::Record(
                        fields
                            .iter()
                            .zip(values)
                            .map(|(field, value)| (field.name.clone(), settle(value)))
                            .collect(),
                    )
                } else {
                    self.built(path, fields, &values, expr.span)
                }
            }
            // LR13.2: a map literal is a `Map<K, V>` of what its entries hold.
            ExprKind::Map(entries) => {
                let mut key_type = Type::Unresolved;
                let mut value_type = Type::Unresolved;
                for (i, entry) in entries.iter().enumerate() {
                    let key = match &entry.key {
                        MapKey::Name(_) => Type::Primitive(Primitive::String),
                        MapKey::Computed(key) => settle(self.expr(key)),
                    };
                    let value = settle(self.expr(&entry.value));
                    (key_type, value_type) = if i == 0 {
                        (key, value)
                    } else {
                        (unify(key_type, key), unify(value_type, value))
                    };
                }
                Type::Builtin {
                    kind: Builtin::Map,
                    args: vec![key_type, value_type],
                }
            }
            ExprKind::Set(items) => {
                let mut element = Type::Unresolved;
                for (i, item) in items.iter().enumerate() {
                    let held = settle(self.expr(item));
                    element = if i == 0 { held } else { unify(element, held) };
                }
                Type::Builtin {
                    kind: Builtin::Set,
                    args: vec![element],
                }
            }
            ExprKind::Function { .. } => self.function_expr(expr, &[]),
            ExprKind::Match { scrutinee, arms } => self.match_expr(scrutinee, arms, None),
            ExprKind::If {
                branches,
                otherwise,
            } => self.if_expr(branches, otherwise, None),
            ExprKind::Error => Type::Unresolved,
        }
    }

    /// The type of `name` read from a value of type `held`.
    fn member(&mut self, held: &Type, name: &str, span: Span) -> Type {
        if !self.settled(held, name, span) {
            return Type::Unresolved;
        }

        if let Some(found) = self.stored(held, name) {
            self.member_visibility(found.visibility, found.module, &found.owner, name, span);
            return found.ty;
        }

        // LR13: `length` is how many elements a collection holds.
        if is_collection(held) && name == "length" {
            return Type::Primitive(Primitive::I64);
        }

        // LR37: a string exposes its storage size in bytes.
        if matches!(held, Type::Primitive(Primitive::String)) && name == "byteLength" {
            return Type::Primitive(Primitive::I64);
        }

        let Some(owner) = self.known(held) else {
            return Type::Unresolved;
        };

        // LR89.1: `:` calls a method and `.` reaches fields, and neither
        // spelling is a fallback for the other.
        let mut reported = Diagnostic::error(
            codes::NO_SUCH_MEMBER,
            span,
            format!("`{owner}` has no member `{name}`"),
        );
        if self.has_method(held, name) {
            reported = reported.note(format!(
                "`{name}` is a method, and a method is called with `:` (LR12.2)."
            ));
        }
        self.diagnostics.push(reported);

        Type::Unresolved
    }

    /// LR27: `await` takes a `Task<T>` and produces the `T`, in the body of
    /// an async function and nowhere else.
    fn awaited(&mut self, held: &Type, span: Span) -> Type {
        if !self.asynchronously.last().copied().unwrap_or(false) {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::AWAIT_OUTSIDE_ASYNC,
                    span,
                    "this function is not async",
                )
                .note("`await` is written in the body of an async function (LR27)."),
            );
        }

        let Type::Builtin {
            kind: Builtin::Task,
            args,
        } = held
        else {
            if !matches!(held, Type::Unresolved) {
                self.diagnostics.push(
                    Diagnostic::error(codes::AWAIT_OPERAND, span, format!("cannot await {held}"))
                        .note("`await` takes the `Task` an async call produces (LR27)."),
                );
            }
            return Type::Unresolved;
        };

        args.first().cloned().unwrap_or(Type::Unresolved)
    }

    fn propagated(&mut self, held: &Type, span: Span) -> Type {
        let Type::Builtin {
            kind: Builtin::Result,
            args,
        } = held
        else {
            if !matches!(held, Type::Unresolved) {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::PROPAGATION_OPERAND,
                        span,
                        format!("cannot propagate {held}"),
                    )
                    .note("`?` propagates the error branch of a `Result` (LR25.2)."),
                );
            }
            return Type::Unresolved;
        };
        let Some(value) = args.first().cloned() else {
            return Type::Unresolved;
        };
        let Some(error) = args.get(1).cloned() else {
            return Type::Unresolved;
        };

        let enclosing = self.returns.last().cloned().flatten();
        let Some(Type::Builtin {
            kind: Builtin::Result,
            args: returned,
        }) = enclosing
        else {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::PROPAGATION_RETURN,
                    span,
                    "this function does not return `Result`",
                )
                .note("An error propagated with `?` returns from the enclosing function (LR25.2)."),
            );
            return value;
        };
        let Some(wanted) = returned.get(1).cloned() else {
            return value;
        };

        if error == wanted
            || matches!(error, Type::Unresolved)
            || matches!(wanted, Type::Unresolved)
        {
            return value;
        }

        let conversion = self
            .find_method(&error, "into", span)
            .and_then(|(overloads, _)| {
                overloads.into_iter().find(|signature| {
                    signature.takes_self
                        && signature.params.is_empty()
                        && signature.type_params.is_empty()
                        && self.accepts(&wanted, &signature.result)
                })
            });

        match conversion {
            Some(conversion) => self.facts.record_call(span, conversion.span),
            None => self.diagnostics.push(
                Diagnostic::error(
                    codes::PROPAGATION_CONVERSION,
                    span,
                    format!("`{error}` does not convert into `{wanted}`"),
                )
                .note("The error branch converts through `Into` before `?` returns it (LR25.2, LR35)."),
            ),
        }

        value
    }

    /// LR18: reports every member `claimed` is missing from what `wanted`
    /// requires, or has with a signature that does not match.
    pub(super) fn conforms(&mut self, claimed: &Type, wanted: &Type, span: Span) {
        let Type::Named { module, name, args } = wanted else {
            return;
        };
        let Some(Decl::Interface(interface)) = self.table.get(*module, name) else {
            return;
        };

        let owner = match claimed {
            Type::Named { name, .. } => name.clone(),
            other => other.to_string(),
        };

        for (member, required) in &interface.methods {
            for required in required {
                let held = self.methods_of(claimed, member).is_some_and(|had| {
                    let required =
                        filled(std::slice::from_ref(required), &interface.type_params, args);
                    let required = against(&required[0], claimed);
                    had.iter().any(|had| same_signature(had, &required))
                });
                if held {
                    continue;
                }

                let has_name = self.methods_of(claimed, member).is_some();
                let complaint = if has_name {
                    format!(
                        "`{owner}` has `{member}`, and not with the signature `{name}` requires"
                    )
                } else {
                    format!("`{owner}` does not have `{member}`, which `{name}` requires")
                };

                self.diagnostics.push(
                    Diagnostic::error(codes::INTERFACE_NOT_SATISFIED, span, complaint)
                        .label(required.span, "required here")
                        .note("Saying `implements` is a promise to have every member (LR18)."),
                );
            }
        }

        for property in &interface.properties {
            let required = substitute(&property.ty, &interface.type_params, args);
            let held = self
                .stored(claimed, &property.name)
                .is_some_and(|found| found.ty == required);
            if held {
                continue;
            }

            self.diagnostics.push(
                Diagnostic::error(
                    codes::INTERFACE_NOT_SATISFIED,
                    span,
                    format!(
                        "`{owner}` does not have `{}: {}`, which `{name}` requires",
                        property.name, required
                    ),
                )
                .note("Saying `implements` is a promise to have every member (LR18)."),
            );
        }
    }

    /// LR12.2: a struct literal gives a value for every field the struct
    /// declares without a default, and names no field it does not declare.
    /// What `container[key]` reads, and what it takes for a key (LR37, LR69).
    fn indexed(&mut self, container: &Type, key: &Type, key_span: Span, span: Span) -> Type {
        // LR37: a string is UTF-8, and an index into one would have to pretend
        // otherwise.
        if *container == Type::STRING {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::STRING_NOT_INDEXABLE,
                    span,
                    "a string is not indexed by integer",
                )
                .note(
                    "UTF-8 has no constant-time character at an index. \
                     Read it with `bytes()`, `chars()`, or `graphemes()` (LR37).",
                ),
            );
            return Type::Unresolved;
        }

        if let Type::Builtin {
            kind: Builtin::RangeExclusive | Builtin::RangeInclusive,
            args: bounds,
        } = key
            && let Type::Builtin {
                kind: Builtin::List | Builtin::Slice,
                args,
            } = container
        {
            let int = Type::Primitive(Primitive::I64);
            if let Some(bound) = bounds.first()
                && !self.accepts(&int, bound)
            {
                self.diagnostics.push(Diagnostic::error(
                    codes::INDEX_TYPE,
                    key_span,
                    format!("a slice range is bounded by `int`, not {}", article(bound)),
                ));
            }
            return Type::Builtin {
                kind: Builtin::Slice,
                args: vec![args.first().cloned().unwrap_or(Type::Unresolved)],
            };
        }

        let (wanted, element) = match container {
            Type::Builtin {
                kind: Builtin::Map | Builtin::FrozenMap,
                args,
            } => {
                let value = args.get(1).cloned().unwrap_or(Type::Unresolved);
                (args.first().cloned(), value.optional())
            }
            Type::Builtin {
                kind: Builtin::List | Builtin::FrozenList | Builtin::Slice,
                args,
            } => (
                Some(Type::Primitive(Primitive::I64)),
                args.first().cloned().unwrap_or(Type::Unresolved),
            ),
            Type::Array(element, _) => (
                Some(Type::Primitive(Primitive::I64)),
                element.as_ref().clone(),
            ),
            Type::Primitive(Primitive::Bytes) => (
                Some(Type::Primitive(Primitive::I64)),
                Type::Primitive(Primitive::U8),
            ),
            // LR36: every other type is indexed through `Index`.
            other => {
                return self.overloaded("[]", "Index", "index", other, Some((key, key_span)), span);
            }
        };

        if let Some(wanted) = wanted
            && !self.accepts(&wanted, key)
        {
            self.diagnostics.push(Diagnostic::error(
                codes::INDEX_TYPE,
                key_span,
                format!(
                    "this is keyed by `{wanted}`, and the index is {}",
                    article(key)
                ),
            ));
        }

        element
    }

    /// The type a `Path { ... }` literal builds: a struct, or the enum a
    /// record variant belongs to (LR12.2, LR15.3).
    fn built(
        &mut self,
        path: &[String],
        written: &[FieldInit],
        values: &[Type],
        span: Span,
    ) -> Type {
        if let [owner, variant] = path
            && let Some((built, Variant::Record(fields))) = self.variant(owner, variant)
        {
            let Type::Named { module, .. } = &built else {
                return built;
            };
            let module = *module;
            self.initializers(
                &format!("{owner}.{variant}"),
                module,
                &fields,
                written,
                values,
                span,
            );
            return built;
        }

        let built = self
            .types
            .named(path, Vec::new())
            .unwrap_or(Type::Unresolved);

        let Type::Named { module, name, .. } = &built else {
            return built;
        };
        let (module, name) = (*module, name.clone());

        let Some(structure) = self.table.structure(module, &name) else {
            return built;
        };
        let (params, mut fields) = (structure.type_params.clone(), structure.fields.clone());

        // LR19: a generic struct takes its type arguments from the values it
        // is built with, the way a generic call takes them from what it
        // passes.
        let mut bound = BTreeMap::new();
        for (field, value) in written.iter().zip(values) {
            if let Some(declared) = fields.iter().find(|declared| declared.name == field.name) {
                infer(&params, &declared.ty, value, &mut bound);
            }
        }
        // LR19: what no field settles is read from the type the literal is
        // used at.
        if let Some(expected) = self.expected.take() {
            let itself = Type::Named {
                module,
                name: name.clone(),
                args: params.iter().cloned().map(Type::Parameter).collect(),
            };
            infer(&params, &itself, &expected, &mut bound);
        }

        let args: Vec<Type> = params
            .iter()
            .map(|param| bound.get(param).cloned().unwrap_or(Type::Unresolved))
            .collect();
        self.unknown_type_args(&params, &args, values, span);

        for field in &mut fields {
            field.ty = substitute(&field.ty, &params, &args);
        }

        self.initializers(&name, module, &fields, written, values, span);

        Type::Named { module, name, args }
    }

    /// The enum variant `owner.name` names, and the enum it builds (LR15.3).
    pub(super) fn variant(&self, owner: &str, name: &str) -> Option<(Type, Variant)> {
        // A local of that name holds a value, and a value is not a type.
        if self.shadowed(owner) {
            return None;
        }

        let named = self
            .types
            .named(std::slice::from_ref(&owner.to_owned()), Vec::new())?;
        let Type::Named {
            module,
            name: enumeration,
            ..
        } = named
        else {
            return None;
        };
        let Some(Decl::Enum(declared)) = self.table.get(module, &enumeration) else {
            return None;
        };

        let payload = declared.variants.get(name)?;
        let unknown: Vec<Type> = declared
            .type_params
            .iter()
            .map(|_| Type::Unresolved)
            .collect();

        let payload = match payload {
            Variant::Unit => Variant::Unit,
            Variant::Tuple(types) => Variant::Tuple(
                types
                    .iter()
                    .map(|ty| substitute(ty, &declared.type_params, &unknown))
                    .collect(),
            ),
            Variant::Record(fields) => Variant::Record(
                fields
                    .iter()
                    .map(|field| Field {
                        ty: substitute(&field.ty, &declared.type_params, &unknown),
                        ..field.clone()
                    })
                    .collect(),
            ),
        };

        Some((
            Type::Named {
                module,
                name: enumeration,
                args: unknown,
            },
            payload,
        ))
    }

    fn initializers(
        &mut self,
        owner: &str,
        module: ModuleId,
        declared: &[Field],
        written: &[FieldInit],
        values: &[Type],
        span: Span,
    ) {
        let name = owner;

        for (field, value) in written.iter().zip(values) {
            let Some(declared) = declared.iter().find(|declared| declared.name == field.name)
            else {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::UNKNOWN_FIELD,
                        field.span,
                        format!("`{name}` has no field `{}`", field.name),
                    )
                    .note("A literal names the fields the type declares (LR12.2, LR15.3)."),
                );
                continue;
            };

            let (visibility, wanted) = (declared.visibility, declared.ty.clone());
            self.member_visibility(visibility, module, name, &field.name, field.span);
            self.expect(&wanted, value, field.value.span);
        }

        let missing: Vec<String> = declared
            .iter()
            .filter(|declared| !declared.optional)
            .filter(|declared| !written.iter().any(|field| field.name == declared.name))
            .map(|declared| format!("`{}`", declared.name))
            .collect();

        if !missing.is_empty() {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::MISSING_FIELD,
                    span,
                    format!("this `{name}` is missing {}", missing.join(", ")),
                )
                .note("A field is left out only where it is declared with a default (LR12.2)."),
            );
        }
    }

    /// Checks a member against its module or package boundary (LR44).
    pub(super) fn member_visibility(
        &mut self,
        visibility: Option<Visibility>,
        owner: ModuleId,
        declared: &str,
        name: &str,
        span: Span,
    ) {
        if self.member_is_visible(visibility, owner) {
            return;
        }

        let (level, boundary) = match visibility {
            Some(Visibility::Private) => ("private", "module"),
            Some(Visibility::Internal) => ("internal", "package"),
            _ => return,
        };
        self.diagnostics.push(
            Diagnostic::error(
                codes::PRIVATE_MEMBER,
                span,
                format!("`{name}` is {level} to the {boundary} that declares `{declared}`"),
            )
            .note(format!(
                "A member written `{level}` is reachable only in that {boundary} (LR44)."
            )),
        );
    }

    pub(super) fn member_is_visible(
        &self,
        visibility: Option<Visibility>,
        owner: ModuleId,
    ) -> bool {
        match visibility {
            Some(Visibility::Private) => owner == self.scope,
            Some(Visibility::Internal) => {
                self.graph.module(owner).package == self.graph.module(self.scope).package
            }
            None | Some(Visibility::Public) => true,
        }
    }

    /// Whether it is settled what `held` holds, which is what a member of it
    /// can be read from (LR8, LR17.2).
    pub(super) fn settled(&mut self, held: &Type, name: &str, span: Span) -> bool {
        // LR8, LR20: a method a block adds to the optional is a method of the
        // optional, not of what it holds.
        if held.is_optional() && self.extension_adds(held, name) {
            return true;
        }
        if held.is_optional() {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::MEMBER_THROUGH_OPTIONAL,
                    span,
                    format!("`{held}` may hold nothing, and `{name}` is read from what it holds"),
                )
                .note("Check it with `~= nil` first, or reach through it with `?.` (LR8)."),
            );
            return false;
        }

        if let Type::Union(members) = held {
            let spellings: Vec<String> = members.iter().map(ToString::to_string).collect();
            self.diagnostics.push(
                Diagnostic::error(
                    codes::MEMBER_THROUGH_UNION,
                    span,
                    format!(
                        "`{held}` holds {}, and each has members of its own",
                        spellings.join(" or ")
                    ),
                )
                .note("Settle which it is with `is`, or with `match` (LR17.2, LR57)."),
            );
            return false;
        }

        true
    }

    pub(super) fn name(&mut self, name: &str) -> Type {
        let declared = self.unnarrowed(name);

        // What a condition proved wins over what the declaration said, for as
        // long as the branch that proved it lasts (LR57).
        self.proved(&Place::name(name)).unwrap_or(declared)
    }

    /// The type `name` was declared with, with nothing a condition proved
    /// laid over it.
    pub(super) fn unnarrowed(&mut self, name: &str) -> Type {
        let found = self
            .values
            .iter()
            .enumerate()
            .rev()
            .find_map(|(index, scope)| scope.get(name).cloned().map(|ty| (index, ty)));

        let Some((index, ty)) = found else {
            return Type::Unresolved;
        };

        for closure in &mut self.closures {
            if index < closure.base {
                closure
                    .values
                    .entry(name.to_owned())
                    .or_insert_with(|| ty.clone());
            }
        }

        ty
    }

    /// The module-level `const` a name reads where no binding of the walk
    /// holds it: one of this module, or one imported (LR21.1, LR24).
    fn module_constant(&self, name: &str) -> Option<(ModuleId, String, Type)> {
        if self.values.iter().any(|scope| scope.contains_key(name)) {
            return None;
        }
        let (module, declared) = match &self.names.scope(self.scope).get(name)?.origin {
            Origin::Binding { constant: true, .. } => (self.scope, name.to_owned()),
            Origin::Imported { module, name } => (*module, name.clone()),
            _ => return None,
        };
        match self.table.get(module, &declared)? {
            Decl::Constant { ty } => Some((module, declared, ty.clone())),
            _ => None,
        }
    }

    /// Whether `name` is declared but the table holds nothing for it, which
    /// only a compile-time function leaves behind (LR23.1).
    fn compile_time_function(&self, name: &str) -> bool {
        if self.values.iter().any(|scope| scope.contains_key(name)) {
            return false;
        }
        let Some(binding) = self.names.scope(self.scope).get(name) else {
            return false;
        };
        let (module, declared) = match &binding.origin {
            Origin::Declared { .. } => (self.scope, name),
            Origin::Imported { module, name } => (*module, name.as_str()),
            Origin::Binding { .. } | Origin::Namespace(_) => return false,
        };
        self.table.get(module, declared).is_none()
    }
}

pub(super) fn result_variant(expr: &Expr) -> Option<&str> {
    let ExprKind::Field { receiver, name, .. } = &expr.kind else {
        return None;
    };
    let ExprKind::Name(owner) = &receiver.kind else {
        return None;
    };
    (owner == "Result" && matches!(name.as_str(), "Ok" | "Err")).then_some(name)
}

/// The type of the member called `name`, or unresolved where the type has no
/// such member. A missing member is reported where it is read, not here.
pub(super) fn field_type(fields: &[Field], name: &str) -> Type {
    fields
        .iter()
        .find(|field| field.name == name)
        .map_or(Type::Unresolved, |field| field.ty.clone())
}
