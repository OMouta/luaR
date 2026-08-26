//! Giving every written type and every expression a type, and reporting the
//! programs that are wrong about them (LR4.2, LR5.1, LR7, LR11.1, LR54).
//!
//! Two jobs share one walk. Every type written in the source is resolved,
//! which is where a name that is not a type is reported, and every expression
//! is given a type, which is where a value that cannot be what it is used as
//! is reported.
//!
//! The checker is deliberately incomplete and knows it. A call, a field, and
//! anything reaching into another module are [`Type::Unresolved`] until the
//! stages that answer them exist, and an unresolved type never causes a
//! diagnostic. What is reported is what the compiler can be sure of today.

use std::collections::{BTreeMap, HashMap};

use luar_ast::{
    Argument, ArmBody, BinaryOp, Binding, Block, Expr, ExprKind, FieldInit, Function, FunctionBody,
    InterpolationPart, Item, MapKey, MatchArm, Member, Module, Param, Pattern, PatternKind,
    Payload, Property, Stmt, StmtKind, Struct, UnaryOp, Visibility,
};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::aliases::substitute;
use crate::annotations::Resolver;
use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin, bound};
use crate::table::{Decl, Field, Overloads, Signature, Table, Variant};
use crate::types::{Builtin, Primitive, Type};

/// Checks the types of every module in `graph`.
#[must_use]
pub fn check(graph: &Graph, names: &Names, table: &Table) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    for (id, node) in graph.modules() {
        let mut checker = Checker {
            names,
            table,
            types: Resolver::new(names, table.kinds(), table.aliases(), id),
            scope: id,
            values: vec![HashMap::new()],
            extensions: extensions(names, table, id),
            returns: Vec::new(),
            narrowed: Vec::new(),
            diagnostics: &mut diagnostics,
        };
        checker.module(&node.ast);
    }

    diagnostics
}

struct Checker<'a> {
    names: &'a Names,
    /// What every declaration is. A type written in a declaration was
    /// resolved when the table was built, so the checker reads it from there
    /// rather than resolving it a second time.
    table: &'a Table,
    /// Resolves the types written inside a body, which the table does not
    /// hold.
    types: Resolver<'a>,
    scope: ModuleId,
    /// What each name in scope holds, innermost last.
    values: Vec<HashMap<String, Type>>,
    /// The extension blocks this module may reach (LR20).
    extensions: Vec<Extension<'a>>,
    /// What the function being walked declares it returns, innermost last
    /// (LR9.1). `None` where nothing was written down to check against.
    returns: Vec<Option<Type>>,
    /// What conditions have proved about names in scope, innermost last
    /// (LR57). Kept apart from `values` so that a name declared again inside
    /// a branch is a new name rather than the narrowed one.
    narrowed: Vec<HashMap<String, Type>>,
    diagnostics: &'a mut Vec<Diagnostic>,
}

/// A field or property found on a type, and the declaration it came from.
struct Found {
    module: ModuleId,
    owner: String,
    visibility: Option<Visibility>,
    ty: Type,
}

/// What a condition proves about one name where it holds, and where it does
/// not (LR57).
struct Narrowing {
    name: String,
    when_true: Type,
    when_false: Type,
}

/// What a call resolved to.
struct Callee {
    /// What the call writes, for a diagnostic to name.
    name: String,
    /// Every signature that name has (LR40).
    overloads: Overloads,
    /// Where the call names the type or the block, the type the receiver
    /// takes as the first argument (LR12.2). `point:length()` is
    /// `Vec2.length(point)` written out, and both are checked the same way.
    receiver: Option<Type>,
}

/// How a call lines up with one signature (LR9.1, LR9.4, LR9.5, LR9.6).
struct Fit {
    /// The parameter each argument fills, where it fills one.
    slots: Vec<Option<usize>>,
    /// Whether every parameter needing an argument got one, and none spilled.
    counted: bool,
}

/// What one case of a match covers (LR16.4).
enum Covers {
    /// Every value, which is what a wildcard and a bare binding match.
    Anything,
    /// One case of a closed type, named as a pattern writes it.
    Case(String),
}

/// What `pattern` covers, where that is something this stage can name.
///
/// A pattern that only sometimes matches, such as a literal or a variant
/// whose payload is itself matched, covers nothing that can be counted.
fn covers(pattern: &Pattern) -> Option<Covers> {
    match &pattern.kind {
        PatternKind::Wildcard | PatternKind::Binding(_) => Some(Covers::Anything),
        PatternKind::Path { segments, payload } => {
            let bound = match payload {
                None => true,
                Some(Payload::Tuple(patterns)) => patterns.iter().all(irrefutable),
                // A field left out is a field not tested, so what decides it
                // is whether the listed ones rule anything out.
                Some(Payload::Record { fields, .. }) => {
                    fields.iter().all(|field| match &field.pattern {
                        Some(pattern) => irrefutable(pattern),
                        None => true,
                    })
                }
            };

            bound.then(|| Covers::Case(segments.join(".")))
        }
        // `true` and `false` are the cases of `bool`, and are written as
        // literals rather than as a path.
        PatternKind::Literal(literal) => match &literal.kind {
            ExprKind::Bool(value) => Some(Covers::Case(value.to_string())),
            _ => None,
        },
        _ => None,
    }
}

/// Whether `pattern` matches whatever it is given, so that it rules nothing
/// out (LR16.2).
fn irrefutable(pattern: &Pattern) -> bool {
    match &pattern.kind {
        PatternKind::Wildcard | PatternKind::Binding(_) => true,
        PatternKind::Tuple(patterns) => patterns.iter().all(irrefutable),
        _ => false,
    }
}

/// Whether two signatures are the same to a caller: same parameters, same
/// result, and the same about `self` and `async` (LR18, LR40).
fn same_signature(left: &Signature, right: &Signature) -> bool {
    left.takes_self == right.takes_self
        && left.asynchronous == right.asynchronous
        && left.result == right.result
        && left.params.len() == right.params.len()
        && left
            .params
            .iter()
            .zip(&right.params)
            .all(|(left, right)| left.ty == right.ty)
}

/// Lines a call up with one signature, without reporting anything.
fn fit(signature: &Signature, args: &[Argument]) -> Fit {
    let params = &signature.params;
    let variadic = params.last().is_some_and(|param| param.variadic);
    let mut filled = vec![false; params.len()];
    let mut slots = Vec::with_capacity(args.len());
    let mut position = 0;

    for argument in args {
        let index = match &argument.name {
            // LR9.5: a named argument names a parameter.
            Some(name) => params.iter().position(|param| &param.name == name),
            None => {
                let index = position;
                position += 1;
                // Everything from a variadic onward goes to it (LR9.6).
                Some(index.min(params.len().saturating_sub(1)))
                    .filter(|_| index < params.len() || (variadic && !params.is_empty()))
            }
        };

        if let Some(index) = index {
            filled[index] = true;
        }
        slots.push(index);
    }

    let missing = params
        .iter()
        .zip(&filled)
        .any(|(param, filled)| !param.optional && !filled);

    Fit {
        slots,
        counted: variadic || (!missing && position <= params.len()),
    }
}

/// Whether the overloads of one method take `self`, which every overload of
/// one method does or none does (LR65).
fn takes_self(overloads: &Overloads) -> bool {
    overloads
        .first()
        .is_some_and(|signature| signature.takes_self)
}

/// Types as a diagnostic writes them, comma separated.
fn list(types: &[Type]) -> String {
    types
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

/// The signature the declaration at `span` produced, out of the overloads its
/// name has (LR40). A body is checked against its own signature, not against
/// whichever one happens to be first.
fn written(overloads: Option<&Overloads>, span: Span) -> Option<&Signature> {
    overloads?.iter().find(|signature| signature.span == span)
}

/// An extension block a module can use, under the name that module knows it
/// by, which `as` may have changed (LR20, LR21.1).
struct Extension<'a> {
    name: &'a str,
    target: &'a Type,
    methods: &'a BTreeMap<String, Overloads>,
}

/// The extension blocks in scope in `module`: the ones it declares and the
/// ones it imports by name (LR20).
///
/// A namespace import binds the other module, not the blocks inside it, so it
/// brings no extension into scope. Importing a module for one function never
/// changes what an unrelated method call means.
fn extensions<'a>(names: &'a Names, table: &'a Table, module: ModuleId) -> Vec<Extension<'a>> {
    let mut found = Vec::new();

    for (local, binding) in names.scope(module).names() {
        let decl = match &binding.origin {
            Origin::Declared { .. } => table.get(module, local),
            Origin::Imported { module, name } => table.get(*module, name),
            Origin::Binding { .. } | Origin::Namespace(_) => continue,
        };

        if let Some(Decl::Extension { target, methods }) = decl {
            found.push(Extension {
                name: local,
                target,
                methods,
            });
        }
    }

    found
}

impl Checker<'_> {
    fn module(&mut self, module: &Module) {
        for item in &module.items {
            self.item(item);
        }
    }

    fn item(&mut self, item: &Item) {
        match item {
            // A declaration the table holds was resolved when the table was
            // built, so its body is checked against what is recorded there.
            Item::Function(function) => {
                // LR20: a qualified name writes a member of the type it
                // names, so its body reads `self` as that type.
                let (overloads, receiver) = match function.name.as_slice() {
                    [name] => (self.table.overloads(self.scope, name), None),
                    [owner, name] => match self.table.structure(self.scope, owner) {
                        Some(structure) => {
                            (structure.methods.get(name), Some(self.receiver(owner)))
                        }
                        None => (None, None),
                    },
                    _ => (None, None),
                };

                let signature = written(overloads, function.span).cloned();
                self.body(function, signature.as_ref(), receiver);
            }
            Item::Struct(structure) => self.structure(structure),
            Item::Extend(extend) => {
                let (target, methods) = match self.table.get(self.scope, &extend.name) {
                    Some(Decl::Extension { target, methods }) => (target.clone(), methods.clone()),
                    _ => (Type::Unresolved, BTreeMap::new()),
                };

                for function in &extend.functions {
                    let name = function.name.last();
                    if let Some(name) = name {
                        self.overrides(&target, name, function.span);
                    }
                    let receiver = match &target {
                        Type::Unresolved => None,
                        target => Some(target.clone()),
                    };
                    let signature = written(name.and_then(|name| methods.get(name)), function.span);
                    self.body(function, signature, receiver);
                }
            }
            // Nothing of these is written outside their own types, which the
            // table already read.
            Item::Enum(_) | Item::Interface(_) | Item::TypeAlias(_) => {}
            Item::Conditional(conditional) => {
                for (_, items) in &conditional.branches {
                    for item in items {
                        self.item(item);
                    }
                }
                for item in conditional.otherwise.iter().flatten() {
                    self.item(item);
                }
            }
            Item::Import(_) => {}
            Item::Stmt(stmt) => self.stmt(stmt),
        }
    }

    /// The type a member of `name` reads `self` as, which is the type
    /// itself, standing for its own parameters (LR65, LR19).
    fn receiver(&self, name: &str) -> Type {
        let args = match self.table.structure(self.scope, name) {
            Some(structure) => structure
                .type_params
                .iter()
                .map(|param| Type::Parameter(param.clone()))
                .collect(),
            None => Vec::new(),
        };

        Type::Named {
            module: self.scope,
            name: name.to_owned(),
            args,
        }
    }

    fn structure(&mut self, structure: &Struct) {
        let Some(declared) = self.table.structure(self.scope, &structure.name).cloned() else {
            return;
        };

        // LR18: conformance is nominal, so saying `implements` is a promise
        // the declaration has to keep.
        let claimed = Type::Named {
            module: self.scope,
            name: structure.name.clone(),
            args: Vec::new(),
        };
        for (written, resolved) in structure.implements.iter().zip(&declared.implements) {
            self.conforms(&claimed, resolved, written.span);
        }

        // LR65: `self` in a member is the type the member is declared in.
        let receiver = self.receiver(&structure.name);

        self.types.enter(&structure.type_params);

        for member in &structure.members {
            match member {
                Member::Field(field) => {
                    if let Some(default) = &field.default {
                        let value = self.expr(default);
                        let wanted = field_type(&declared.fields, &field.name);
                        self.expect(&wanted, &value, default.span);
                    }
                }
                Member::Function { function, .. } => {
                    let overloads = function
                        .name
                        .last()
                        .and_then(|name| declared.methods.get(name));
                    let signature = written(overloads, function.span).cloned();
                    self.body(function, signature.as_ref(), Some(receiver.clone()));
                }
                Member::Property(property) => {
                    let held = field_type(&declared.properties, &property.name);
                    self.property(property, held, receiver.clone());
                }
            }
        }

        self.types.leave();
    }

    /// A property reads and writes one type, and its accessors take no
    /// parameters of their own (LR43, LR65).
    fn property(&mut self, property: &Property, held: Type, receiver: Type) {
        // LR43: a property reads like a field, and a field never hands back a
        // failure the caller has to unwrap.
        if matches!(
            held,
            Type::Builtin {
                kind: Builtin::Result,
                ..
            }
        ) {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::FALLIBLE_PROPERTY,
                    property.span,
                    format!(
                        "`{}` is a property, and gives back a `Result`",
                        property.name
                    ),
                )
                .note("Anything that can fail is a method, and reads like one (LR43)."),
            );
        }

        self.push();
        self.bind("self", receiver.clone());
        self.returns.push(Some(held.clone()));
        self.block(&property.get);
        self.returns.pop();
        self.pop();

        if let Some(setter) = &property.set {
            self.push();
            self.bind("self", receiver);
            self.bind(&setter.param, held);
            self.returns.push(Some(Type::Tuple(Vec::new())));
            self.block(&setter.body);
            self.returns.pop();
            self.pop();
        }
    }

    /// Checks a function body against its signature.
    ///
    /// A signature the table holds was resolved once, when the table was
    /// built. One it does not hold, such as a method written outside the type
    /// it belongs to, is resolved here instead, and so is resolved once too.
    fn body(&mut self, function: &Function, signature: Option<&Signature>, receiver: Option<Type>) {
        self.types.enter(&function.type_params);
        self.push();

        if let Some(receiver) = receiver {
            self.bind("self", receiver);
        }

        // LR65: `self` is written like a parameter, but its type is the
        // receiver bound above rather than anything the parameter list says.
        // Binding it again here would replace that with nothing.
        let params = match signature {
            Some(signature) if signature.takes_self => function.params.get(1..).unwrap_or_default(),
            _ => function.params.as_slice(),
        };

        for (index, param) in params.iter().enumerate() {
            let declared = match signature {
                Some(signature) => signature
                    .params
                    .get(index)
                    .map_or(Type::Unresolved, |param| param.ty.clone()),
                None => match &param.ty {
                    Some(ty) => self.resolve(ty),
                    None => Type::Unresolved,
                },
            };
            self.param(param, declared);
        }

        let returns = match signature {
            Some(signature) => Some(signature.result.clone()),
            None => function.result.as_ref().map(|result| self.resolve(result)),
        };

        self.returns.push(returns);
        if let Some(body) = &function.body {
            for stmt in &body.stmts {
                self.stmt(stmt);
            }
        }
        self.returns.pop();

        self.pop();
        self.types.leave();
    }

    /// Binds a parameter. One without an annotation is inferred from the call
    /// site, which needs a stage that does not exist yet, so it holds an
    /// unresolved type rather than a wrong one (LR7).
    fn param(&mut self, param: &Param, declared: Type) {
        if let Some(default) = &param.default {
            let value = self.expr(default);
            self.expect(&declared, &value, default.span);
        }

        for name in bound(&param.binding) {
            // A destructured parameter takes the type of a field of what was
            // passed, which is a shape this stage does not take apart yet.
            let held = match &param.binding {
                Binding::Name(_) => declared.clone(),
                _ => Type::Unresolved,
            };
            self.bind(&name, held);
        }
    }

    fn block(&mut self, block: &Block) {
        self.push();
        for stmt in &block.stmts {
            self.stmt(stmt);
        }
        self.pop();
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Local { binding, ty, value } => {
                let value_type = value.as_ref().map(|value| (self.expr(value), value.span));

                let held = match ty {
                    Some(ty) => {
                        let declared = self.resolve(ty);
                        if let Some((value, span)) = &value_type {
                            self.expect(&declared, value, *span);
                        }
                        declared
                    }
                    // LR5.1, LR7: with no annotation the initializer decides.
                    None => value_type.map_or(Type::Unresolved, |(value, _)| settle(value)),
                };

                self.declare(binding, held);
            }
            StmtKind::Const {
                binding, ty, value, ..
            } => {
                let held = self.expr(value);
                let held = match ty {
                    Some(ty) => {
                        let declared = self.resolve(ty);
                        self.expect(&declared, &held, value.span);
                        declared
                    }
                    None => settle(held),
                };

                self.declare(binding, held);
            }
            StmtKind::Assign { target, value, .. } => {
                // LR57: what a branch proved narrows what the name reads as,
                // and never what may be written to it. The declaration says
                // that, and the declaration has not changed.
                let wanted = match &target.kind {
                    ExprKind::Name(name) => self.unnarrowed(name),
                    _ => self.expr(target),
                };
                let held = self.expr(value);
                self.expect(&wanted, &held, value.span);

                // LR57: what was proved held for the value that was there,
                // and the value that is there now was never checked.
                if let ExprKind::Name(name) = &target.kind {
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

                for branch in branches {
                    self.narrow(&failed, false);
                    self.condition(&branch.condition);
                    let facts = self.facts(&branch.condition);

                    self.narrow(&facts, true);
                    self.block(&branch.body);
                    self.widen();

                    self.widen();
                    failed.extend(facts);
                }

                if let Some(otherwise) = otherwise {
                    self.narrow(&failed, false);
                    self.block(otherwise);
                    self.widen();
                }
            }
            StmtKind::While {
                condition, body, ..
            } => {
                self.condition(condition);
                let facts = self.facts(condition);

                self.narrow(&facts, true);
                self.block(body);
                self.widen();
            }
            StmtKind::Repeat { body, until, .. } => {
                // `until` reads the body's bindings, so it is checked inside
                // the body's scope (LR10.3).
                self.push();
                for stmt in &body.stmts {
                    self.stmt(stmt);
                }
                self.condition(until);
                self.pop();
            }
            StmtKind::For {
                bindings,
                iterable,
                body,
                ..
            } => {
                self.expr(iterable);
                self.push();
                for binding in bindings {
                    // What an iterator yields needs the iterator protocol
                    // (LR35), which is not resolved here.
                    self.declare(binding, Type::Unresolved);
                }
                self.block(body);
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
            StmtKind::Unsafe(body) => self.block(body),
            StmtKind::Match { scrutinee, arms } => {
                let held = self.expr(scrutinee);
                for arm in arms {
                    self.arm(arm);
                }
                self.exhaustive(&held, arms, scrutinee.span);
            }
            StmtKind::Return(value) => {
                let wanted = self.returns.last().cloned().flatten();

                match (value, wanted) {
                    (Some(value), Some(wanted)) => {
                        let held = self.expr(value);
                        self.expect_return(&wanted, &held, value.span);
                    }
                    (Some(value), None) => {
                        self.expr(value);
                    }
                    // LR9.1: a bare `return` leaves a function that declares
                    // no result, and leaves nothing behind for one that does.
                    (None, Some(wanted)) => {
                        self.expect_return(&wanted, &Type::Tuple(Vec::new()), stmt.span);
                    }
                    (None, None) => {}
                }
            }
            StmtKind::Expr(expr) => {
                self.expr(expr);
            }
            StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Error => {}
        }
    }

    /// LR16.4: a match over a closed type covers every value it can hold, and
    /// a case an earlier one already covers never runs.
    ///
    /// A guard can fail, so a guarded case covers nothing. Coverage of the
    /// payload of a variant is not worked out here, so a variant counts as
    /// covered only where its payload is matched by names and wildcards.
    fn exhaustive(&mut self, scrutinee: &Type, arms: &[MatchArm], span: Span) {
        let mut covered: BTreeMap<String, Span> = BTreeMap::new();
        let mut anything: Option<Span> = None;

        for arm in arms {
            if let Some(first) = anything {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::UNREACHABLE_CASE,
                        arm.pattern.span,
                        "this case never runs",
                    )
                    .label(first, "everything is already covered here")
                    .note("A case an earlier one covers is an error, not a warning (LR16.4)."),
                );
                continue;
            }

            if arm.guard.is_some() {
                continue;
            }

            match covers(&arm.pattern) {
                Some(Covers::Anything) => anything = Some(arm.pattern.span),
                Some(Covers::Case(name)) => {
                    if let Some(first) = covered.get(&name) {
                        self.diagnostics.push(
                            Diagnostic::error(
                                codes::UNREACHABLE_CASE,
                                arm.pattern.span,
                                format!("`{name}` is covered already"),
                            )
                            .label(*first, "covered here")
                            .note(
                                "A case an earlier one covers is an error, not a warning (LR16.4).",
                            ),
                        );
                    } else {
                        covered.insert(name, arm.pattern.span);
                    }
                }
                None => {}
            }
        }

        // A scrutinee this stage cannot type could hold anything, so what a
        // match over it leaves out is not knowable here.
        if anything.is_some() || matches!(scrutinee, Type::Unresolved) {
            return;
        }

        let Some(closed) = self.closed(scrutinee) else {
            // LR16.4: what is not closed cannot be covered case by case.
            self.diagnostics.push(
                Diagnostic::error(
                    codes::MATCH_NOT_EXHAUSTIVE,
                    span,
                    format!("`{scrutinee}` holds more than this match covers"),
                )
                .note("A value that is not one of a fixed set needs `case _` (LR16.4)."),
            );
            return;
        };

        let missing: Vec<String> = closed
            .into_iter()
            .filter(|case| !covered.contains_key(case))
            .collect();

        if missing.is_empty() {
            return;
        }

        let spellings: Vec<String> = missing.iter().map(|case| format!("`{case}`")).collect();
        self.diagnostics.push(
            Diagnostic::error(
                codes::MATCH_NOT_EXHAUSTIVE,
                span,
                format!("this match does not cover {}", spellings.join(", ")),
            )
            .note("A match over a closed type covers every value of it (LR16.4)."),
        );
    }

    /// Every case a closed type has, spelled as a pattern writes it (LR16.4).
    ///
    /// Enums and `bool` are the closed types this stage can list. An integer,
    /// a string, and a list are not closed at all, and the rest wait for the
    /// coverage rules over tuples and records.
    fn closed(&self, scrutinee: &Type) -> Option<Vec<String>> {
        if *scrutinee == Type::BOOL {
            return Some(vec!["true".to_owned(), "false".to_owned()]);
        }

        let Type::Named { module, name, .. } = scrutinee else {
            return None;
        };
        let Decl::Enum(enumeration) = self.table.get(*module, name)? else {
            return None;
        };

        Some(
            enumeration
                .variants
                .keys()
                .map(|variant| format!("{name}.{variant}"))
                .collect(),
        )
    }

    fn arm(&mut self, arm: &MatchArm) {
        self.push();
        self.pattern(&arm.pattern);
        if let Some(guard) = &arm.guard {
            self.condition(guard);
        }
        match &arm.body {
            ArmBody::Block(block) => self.block(block),
            ArmBody::Expr(expr) => {
                self.expr(expr);
            }
        }
        self.pop();
    }

    /// Binds what a pattern binds, and resolves the types it writes.
    ///
    /// What a pattern binding holds comes from the type being matched, which
    /// needs narrowing (LR57).
    fn pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Binding(name) => self.bind(name, Type::Unresolved),
            PatternKind::Typed { inner, ty } => {
                self.resolve(ty);
                self.pattern(inner);
            }
            PatternKind::Path { payload, .. } => match payload {
                None => {}
                Some(Payload::Tuple(patterns)) => {
                    for pattern in patterns {
                        self.pattern(pattern);
                    }
                }
                Some(Payload::Record { fields, .. }) => {
                    for field in fields {
                        match &field.pattern {
                            Some(pattern) => self.pattern(pattern),
                            None => {
                                let name = field
                                    .bound_as
                                    .clone()
                                    .unwrap_or_else(|| field.field.clone());
                                self.bind(&name, Type::Unresolved);
                            }
                        }
                    }
                }
            },
            PatternKind::Sequence {
                before,
                rest,
                after,
            } => {
                for pattern in before.iter().chain(after) {
                    self.pattern(pattern);
                }
                if let Some(Some(name)) = rest {
                    self.bind(name, Type::Unresolved);
                }
            }
            PatternKind::Tuple(patterns) | PatternKind::Or(patterns) => {
                for pattern in patterns {
                    self.pattern(pattern);
                }
            }
            PatternKind::Wildcard
            | PatternKind::Literal(_)
            | PatternKind::Range { .. }
            | PatternKind::Error => {}
        }
    }

    /// LR4.2: `if`, `elseif`, `while`, `until`, and a match guard take a
    /// `bool`. There is no truthiness to fall back on.
    fn condition(&mut self, expr: &Expr) {
        let held = self.expr(expr);
        if !Type::BOOL.accepts(&held) {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::CONDITION_NOT_BOOL,
                    expr.span,
                    format!("a condition is a `bool`, and this is {held}"),
                )
                .note("LuaR has no truthiness. Compare it, as in `value ~= nil` (LR4.2)."),
            );
        }
    }

    /// The type of an expression.
    fn expr(&mut self, expr: &Expr) -> Type {
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
            ExprKind::Name(name) => self.name(name),
            ExprKind::Unary { op, operand } => self.unary(*op, operand),
            ExprKind::Binary {
                op,
                op_span,
                left,
                right,
            } => self.binary(*op, *op_span, left, right),
            ExprKind::Range { start, end, .. } => {
                for bound in [start, end].into_iter().flatten() {
                    self.expr(bound);
                }
                Type::Unresolved
            }
            ExprKind::Call {
                callee,
                method,
                type_args,
                args,
            } => {
                for ty in type_args {
                    self.resolve(ty);
                }
                let receiver = self.expr(callee);
                self.call(callee, method.as_deref(), &receiver, args, expr.span)
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

                let held = self.expr(receiver);

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
                let held = self.expr(receiver);
                let key = self.expr(index);

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
                self.expr(inner);
                Type::Unresolved
            }
            ExprKind::Cast { value, ty } => {
                self.expr(value);
                self.resolve(ty)
            }
            ExprKind::TypeTest { value, ty } => {
                self.expr(value);
                self.resolve(ty);
                Type::BOOL
            }
            ExprKind::AddressOf { mutable, operand } => {
                let target = self.expr(operand);
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

                // LR12.2: a path names the type being built. Without one the
                // literal is a structural record (LR12.1).
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
            ExprKind::Map(entries) => {
                for entry in entries {
                    if let MapKey::Computed(key) = &entry.key {
                        self.expr(key);
                    }
                    self.expr(&entry.value);
                }
                Type::Unresolved
            }
            ExprKind::Function {
                asynchronous,
                params,
                result,
                body,
            } => {
                self.push();
                let mut types = Vec::with_capacity(params.len());
                for param in params {
                    let declared = match &param.ty {
                        Some(ty) => self.resolve(ty),
                        None => Type::Unresolved,
                    };
                    self.param(param, declared.clone());
                    types.push(declared);
                }

                let returns = match result {
                    Some(result) => self.resolve(result),
                    None => Type::Unresolved,
                };

                self.returns.push(result.as_ref().map(|_| returns.clone()));

                match body.as_ref() {
                    FunctionBody::Block(block) => {
                        for stmt in &block.stmts {
                            self.stmt(stmt);
                        }
                    }
                    FunctionBody::Expr(expr) => {
                        self.expr(expr);
                    }
                }

                self.returns.pop();
                self.pop();

                Type::Function {
                    asynchronous: *asynchronous,
                    params: types,
                    result: Box::new(returns),
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                let held = self.expr(scrutinee);
                for arm in arms {
                    self.arm(arm);
                }
                self.exhaustive(&held, arms, scrutinee.span);
                Type::Unresolved
            }
            ExprKind::If {
                branches,
                otherwise,
            } => {
                for (condition, value) in branches {
                    self.condition(condition);
                    self.expr(value);
                }
                self.expr(otherwise);
                Type::Unresolved
            }
            ExprKind::Error => Type::Unresolved,
        }
    }

    /// The type of `name` read from a value of type `held`.
    ///
    /// Only a struct is taken apart here. Everything else is a shape whose
    /// members need a stage that does not exist yet, and reporting a member
    /// of one as missing would be reporting what the compiler cannot see.
    fn member(&mut self, held: &Type, name: &str, span: Span) -> Type {
        if !self.settled(held, name, span) {
            return Type::Unresolved;
        }

        if let Some(found) = self.stored(held, name) {
            self.private(found.visibility, found.module, &found.owner, name, span);
            return found.ty;
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

    /// LR18: reports every member `claimed` is missing from what `wanted`
    /// requires, or has with a signature that does not match.
    fn conforms(&mut self, claimed: &Type, wanted: &Type, span: Span) {
        let Type::Named { module, name, .. } = wanted else {
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
                let held = self
                    .methods_of(claimed, member)
                    .is_some_and(|had| had.iter().any(|had| same_signature(had, required)));
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
            let held = self
                .stored(claimed, &property.name)
                .is_some_and(|found| found.ty == property.ty);
            if held {
                continue;
            }

            self.diagnostics.push(
                Diagnostic::error(
                    codes::INTERFACE_NOT_SATISFIED,
                    span,
                    format!(
                        "`{owner}` does not have `{}: {}`, which `{name}` requires",
                        property.name, property.ty
                    ),
                )
                .note("Saying `implements` is a promise to have every member (LR18)."),
            );
        }
    }

    /// The overloads of the method `name` on `held`, from the type itself
    /// (LR76). Extensions are left out, because they are in scope where the
    /// call is written and not where the type is declared (LR20).
    fn methods_of(&self, held: &Type, name: &str) -> Option<&Overloads> {
        if let Type::Intersection(parts) = held {
            return parts.iter().find_map(|part| self.methods_of(part, name));
        }

        let Type::Named {
            module,
            name: declared,
            ..
        } = held
        else {
            return None;
        };

        match self.table.get(*module, declared)? {
            Decl::Struct(structure) => structure.methods.get(name),
            Decl::Interface(interface) => interface.methods.get(name),
            _ => None,
        }
    }

    /// Whether a value of type `held` may go where `wanted` is asked for.
    ///
    /// The type rules answer most of it (LR6). What they cannot answer is
    /// interface conformance, which is a claim a declaration makes rather
    /// than a shape a type happens to have (LR18).
    fn accepts(&self, wanted: &Type, held: &Type) -> bool {
        wanted.accepts(held) || self.satisfies(wanted, held)
    }

    /// Whether `held` satisfies the interface `wanted` (LR18).
    fn satisfies(&self, wanted: &Type, held: &Type) -> bool {
        let Type::Named { module, name, .. } = wanted else {
            return false;
        };
        let Some(Decl::Interface(interface)) = self.table.get(*module, name) else {
            return false;
        };

        // A structural interface is satisfied by any type with the members,
        // declared or not. A nominal one has to be claimed.
        if interface.structural {
            return interface.methods.iter().all(|(member, required)| {
                required.iter().all(|required| {
                    self.methods_of(held, member)
                        .is_some_and(|had| had.iter().any(|had| same_signature(had, required)))
                })
            });
        }

        self.implements(held, wanted)
    }

    /// Whether `held` says it implements `wanted` (LR18).
    fn implements(&self, held: &Type, wanted: &Type) -> bool {
        match held {
            Type::Intersection(parts) => parts.iter().any(|part| self.implements(part, wanted)),
            Type::Named { module, name, .. } => match self.table.get(*module, name) {
                Some(Decl::Struct(structure)) => structure
                    .implements
                    .iter()
                    .any(|claim| self.same_interface(claim, wanted)),
                // An interface value is already one of what it requires.
                _ => held == wanted,
            },
            _ => false,
        }
    }

    /// Whether two written interface types name the same declaration.
    fn same_interface(&self, left: &Type, right: &Type) -> bool {
        match (left, right) {
            (
                Type::Named {
                    module: left,
                    name: left_name,
                    ..
                },
                Type::Named {
                    module: right,
                    name: right_name,
                    ..
                },
            ) => left == right && left_name == right_name,
            _ => false,
        }
    }

    /// How a diagnostic names `held`, where the compiler knows every member
    /// it has.
    ///
    /// A decorated declaration grows members when expansion lands (LR23.1),
    /// and everything else is a shape this stage does not model, so a member
    /// of one is not reported as missing from a surface it cannot see.
    fn known(&self, held: &Type) -> Option<String> {
        match held {
            Type::Intersection(parts) => {
                let named: Option<Vec<String>> =
                    parts.iter().map(|part| self.known(part)).collect();
                Some(named?.join(" & "))
            }
            Type::Named {
                module,
                name: declared,
                ..
            } => match self.table.get(*module, declared)? {
                Decl::Struct(structure) if !structure.decorated => Some(declared.clone()),
                Decl::Interface(interface) if !interface.decorated => Some(declared.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether `name` is a method of `held`, which `.` does not reach
    /// (LR89.1).
    fn has_method(&self, held: &Type, name: &str) -> bool {
        match held {
            Type::Intersection(parts) => parts.iter().any(|part| self.has_method(part, name)),
            Type::Named {
                module,
                name: declared,
                ..
            } => match self.table.get(*module, declared) {
                Some(Decl::Struct(structure)) => structure.methods.contains_key(name),
                Some(Decl::Interface(interface)) => interface.methods.contains_key(name),
                _ => false,
            },
            _ => false,
        }
    }

    /// The field or property `name` read off `held`, without reporting.
    ///
    /// An intersection holds every one of its parts at once (LR17.3), so a
    /// member of any part is a member of it.
    fn stored(&self, held: &Type, name: &str) -> Option<Found> {
        if let Type::Intersection(parts) = held {
            return parts.iter().find_map(|part| self.stored(part, name));
        }

        let Type::Named {
            module,
            name: declared,
            ..
        } = held
        else {
            return None;
        };

        let field = match self.table.get(*module, declared)? {
            Decl::Struct(structure) => structure
                .fields
                .iter()
                .chain(&structure.properties)
                .find(|field| field.name == name),
            // An interface requires properties of its own (LR18).
            Decl::Interface(interface) => interface
                .properties
                .iter()
                .find(|property| property.name == name),
            _ => None,
        }?;

        Some(Found {
            module: *module,
            owner: declared.clone(),
            visibility: field.visibility,
            ty: field.ty.clone(),
        })
    }

    /// LR20: an extension adds members to a type, and never replaces one the
    /// type already has. Letting it would make what a call means depend on
    /// which blocks the calling module happens to import.
    fn overrides(&mut self, target: &Type, name: &str, span: Span) {
        let Type::Named {
            module,
            name: declared,
            ..
        } = target
        else {
            return;
        };
        let Some(structure) = self.table.structure(*module, declared) else {
            return;
        };

        if !structure.has_member(name) {
            return;
        }

        self.diagnostics.push(
            Diagnostic::error(
                codes::EXTENSION_OVERRIDES_MEMBER,
                span,
                format!("`{declared}` already has a member `{name}`"),
            )
            .note("An extension adds members to a type and never replaces one (LR20)."),
        );
    }

    /// The extension method `name` on `receiver`, from the blocks this
    /// module has in scope (LR20).
    ///
    /// Two of them offering it is reported here rather than at either block,
    /// because each block is fine on its own and only this call has to pick.
    fn extension(&mut self, receiver: &Type, name: &str, span: Span) -> Option<Overloads> {
        let mut found: Vec<(&str, Overloads)> = self
            .extensions
            .iter()
            .filter(|extension| extension.target == receiver)
            .filter_map(|extension| {
                let overloads = extension.methods.get(name)?;
                Some((extension.name, overloads.clone()))
            })
            .collect();

        if found.len() < 2 {
            return found.pop().map(|(_, overloads)| overloads);
        }

        let blocks: Vec<String> = found
            .iter()
            .map(|(block, _)| format!("`{block}`"))
            .collect();

        self.diagnostics.push(
            Diagnostic::error(
                codes::AMBIGUOUS_EXTENSION,
                span,
                format!("{} both add `{name}` to this type", blocks.join(" and ")),
            )
            .note(format!(
                "Name the block the call means, as in `{}.{name}(value)` (LR20).",
                found[0].0
            )),
        );

        None
    }

    /// LR12.2: a struct literal gives a value for every field the struct
    /// declares without a default, and names no field it does not declare.
    /// What `container[key]` reads, and what it takes for a key (LR37, LR69).
    ///
    /// A missing map key is an ordinary outcome, so a map hands back `V?` and
    /// the caller has to settle it. A list index out of range is a mistake in
    /// the caller's arithmetic, so a list hands back `T` and traps (LR70).
    fn indexed(&mut self, container: &Type, key: &Type, key_span: Span, span: Span) -> Type {
        // LR37: a string is UTF-8, and an index into one would have to
        // pretend otherwise.
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

        let (wanted, element) = match container {
            Type::Builtin {
                kind: Builtin::Map | Builtin::FrozenMap,
                args,
            } => {
                let value = args.get(1).cloned().unwrap_or(Type::Unresolved);
                (args.first().cloned(), value.optional())
            }
            Type::Builtin {
                kind: Builtin::List | Builtin::FrozenList,
                args,
            } => (
                Some(Type::Primitive(Primitive::I64)),
                args.first().cloned().unwrap_or(Type::Unresolved),
            ),
            Type::Array(element) => (
                Some(Type::Primitive(Primitive::I64)),
                element.as_ref().clone(),
            ),
            // Everything else is a container this stage does not model, and
            // what indexing one means waits for the protocol that says so
            // (LR36).
            _ => return Type::Unresolved,
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

        if let Type::Named { module, name, .. } = &built
            && let Some(structure) = self.table.structure(*module, name)
        {
            let (module, name) = (*module, name.clone());
            let fields = structure.fields.clone();
            self.initializers(&name, module, &fields, written, values, span);
        }

        built
    }

    /// The enum variant `owner.name` names, and the enum it builds (LR15.3).
    ///
    /// A generic enum's parameters are left unresolved, because working out
    /// what they hold from the arguments is inference that does not exist yet
    /// (LR19), and a wrong guess would reject a program that is fine.
    fn variant(&self, owner: &str, name: &str) -> Option<(Type, Variant)> {
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
            self.private(visibility, module, name, &field.name, field.span);
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

    /// LR44: a `private` member is reachable only inside the module that
    /// declares it, whichever module holds the value.
    fn private(
        &mut self,
        visibility: Option<Visibility>,
        owner: ModuleId,
        declared: &str,
        name: &str,
        span: Span,
    ) {
        if visibility != Some(Visibility::Private) || owner == self.scope {
            return;
        }

        self.diagnostics.push(
            Diagnostic::error(
                codes::PRIVATE_MEMBER,
                span,
                format!("`{name}` is private to the module that declares `{declared}`"),
            )
            .note("A member written `private` is reachable only in that module (LR44)."),
        );
    }

    /// Whether it is settled what `held` holds, which is what a member of it
    /// can be read from (LR8, LR17.2).
    ///
    /// An optional might hold nothing, and a union holds one of several
    /// things with members of its own. Neither answers what `name` is until a
    /// check has settled which it is (LR57).
    fn settled(&mut self, held: &Type, name: &str, span: Span) -> bool {
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

    /// Checks a call against what it calls, and gives back what it returns.
    ///
    /// A callee this stage cannot name a signature for is left alone: a
    /// closure held in a local, a method of a type it does not model, a
    /// predeclared name. Checking those needs signatures it does not have.
    fn call(
        &mut self,
        callee: &Expr,
        method: Option<&str>,
        receiver: &Type,
        args: &[Argument],
        span: Span,
    ) -> Type {
        let resolved = self.signature_of(callee, method, receiver, span);

        // The arguments are expressions whoever is being called, and whatever
        // is wrong inside one is wrong before any overload is picked.
        let held: Vec<Type> = args
            .iter()
            .map(|argument| self.expr(&argument.value))
            .collect();

        let Some(resolved) = resolved else {
            return Type::Unresolved;
        };

        // LR12.2: naming the type writes the call out in full, so `self` is
        // an ordinary first argument and is counted and checked as one.
        let mut overloads = resolved.overloads;
        if let Some(receiver) = resolved.receiver {
            for signature in &mut overloads {
                signature.params.insert(
                    0,
                    crate::table::Param {
                        name: "self".to_owned(),
                        ty: receiver.clone(),
                        optional: false,
                        variadic: false,
                    },
                );
            }
        }

        // One signature reports against itself, which says more about what is
        // wrong than a list of candidates ever could.
        let signature = match overloads.len() {
            0 => None,
            1 => overloads.into_iter().next(),
            _ => self.overload(&resolved.name, &overloads, args, &held, span),
        };

        let Some(signature) = signature else {
            return Type::Unresolved;
        };

        self.arguments(&signature, args, &held, span);
        signature.result
    }

    /// Whether a call could be calling this signature, which is what makes it
    /// a candidate (LR40).
    fn fits(&self, signature: &Signature, args: &[Argument], held: &[Type]) -> bool {
        let lined_up = fit(signature, args);

        lined_up.counted
            && lined_up
                .slots
                .iter()
                .zip(held)
                .all(|(slot, held)| match slot {
                    Some(index) => self.accepts(&signature.params[*index].ty, held),
                    None => false,
                })
    }

    /// LR40: a call resolves to exactly one overload.
    ///
    /// An argument whose type this stage does not know would fit every
    /// candidate, so a call holding one is left alone rather than reported as
    /// ambiguous against a surface the compiler cannot see.
    fn overload(
        &mut self,
        name: &str,
        overloads: &[Signature],
        args: &[Argument],
        held: &[Type],
        span: Span,
    ) -> Option<Signature> {
        let matching: Vec<&Signature> = overloads
            .iter()
            .filter(|signature| self.fits(signature, args, held))
            .collect();

        if let [only] = matching.as_slice() {
            return Some((*only).clone());
        }

        if held.iter().any(|held| matches!(held, Type::Unresolved)) {
            return None;
        }

        let (code, message) = if matching.is_empty() {
            (
                codes::NO_MATCHING_OVERLOAD,
                format!("no overload of `{name}` takes ({})", list(held)),
            )
        } else {
            (
                codes::AMBIGUOUS_OVERLOAD,
                format!("({}) fits more than one overload of `{name}`", list(held)),
            )
        };

        // Nothing matching means every overload is worth naming; more than
        // one means only the ones that fit are.
        let candidates: Vec<&Signature> = if matching.is_empty() {
            overloads.iter().collect()
        } else {
            matching
        };

        let mut reported = Diagnostic::error(code, span, message);
        for signature in candidates {
            let params: Vec<Type> = signature
                .params
                .iter()
                .map(|param| param.ty.clone())
                .collect();
            reported = reported.label(signature.span, format!("takes ({})", list(&params)));
        }

        self.diagnostics
            .push(reported.note("Overloads are told apart by their parameters (LR40)."));

        None
    }

    /// The signature of what is being called, where the table holds one.
    fn signature_of(
        &mut self,
        callee: &Expr,
        method: Option<&str>,
        receiver: &Type,
        span: Span,
    ) -> Option<Callee> {
        if let Some(method) = method {
            return Some(Callee {
                name: method.to_owned(),
                overloads: self.method(receiver, method, span)?,
                receiver: None,
            });
        }

        match &callee.kind {
            ExprKind::Name(name) => Some(Callee {
                name: name.clone(),
                overloads: self.declared(name)?,
                receiver: None,
            }),
            // LR12.2, LR42, LR76: `Owner.name(...)` is a method call written
            // out, a static, or a call naming the extension block it means. A
            // receiver that is not a plain name is a value, whose members are
            // read rather than named.
            ExprKind::Field {
                receiver: owner,
                name,
                optional: false,
            } => match &owner.kind {
                ExprKind::Name(owner) => self.qualified(owner, name, span),
                _ => None,
            },
            _ => None,
        }
    }

    /// The method `name` on a value of type `receiver`, in the order LR76
    /// states: the type's own methods, then an interface context, then the
    /// extension blocks in scope.
    fn method(&mut self, receiver: &Type, name: &str, span: Span) -> Option<Overloads> {
        if !self.settled(receiver, name, span) {
            return None;
        }

        if let Type::Named {
            module,
            name: declared,
            ..
        } = receiver
        {
            match self.table.get(*module, declared) {
                // An inherent method wins over any extension offering the
                // same name, so adding one shadows the extension rather than
                // changing what a call already meant.
                Some(Decl::Struct(structure)) => {
                    if let Some(overloads) = structure.methods.get(name).cloned() {
                        // Where every overload is private, no call from
                        // outside can reach any of them (LR44).
                        let hidden = overloads
                            .iter()
                            .all(|signature| signature.visibility == Some(Visibility::Private));
                        if hidden {
                            self.private(Some(Visibility::Private), *module, declared, name, span);
                        }
                        return Some(overloads);
                    }
                }
                // A value of interface type dispatches over what the
                // interface requires (LR18.1).
                Some(Decl::Interface(interface)) => {
                    if let Some(overloads) = interface.methods.get(name).cloned() {
                        return Some(overloads);
                    }
                }
                _ => {}
            }
        }

        if let Some(overloads) = self.extension(receiver, name, span) {
            return Some(overloads);
        }

        self.no_such_method(receiver, name, span);
        None
    }

    /// Reports a method nothing offers, where every place one could come from
    /// is known (LR76).
    ///
    /// Most receivers are not. A primitive, a collection, and an enum have
    /// method surfaces this stage does not model, and a decorated declaration
    /// grows members when expansion lands (LR23.1), so a call on one is left
    /// alone rather than reported against a surface the compiler cannot see.
    fn no_such_method(&mut self, receiver: &Type, name: &str, span: Span) {
        let Type::Named {
            module,
            name: declared,
            ..
        } = receiver
        else {
            return;
        };

        let known = match self.table.get(*module, declared) {
            Some(Decl::Struct(structure)) => !structure.decorated,
            Some(Decl::Interface(interface)) => !interface.decorated,
            _ => false,
        };
        if !known {
            return;
        }

        let mut reported = Diagnostic::error(
            codes::NO_SUCH_METHOD,
            span,
            format!("`{declared}` has no method `{name}`"),
        );

        // LR89.1: `:` calls a method and `.` reaches everything else, so a
        // field or a property spelled with `:` is worth saying out loud.
        if let Some(Decl::Struct(structure)) = self.table.get(*module, declared)
            && structure.has_member(name)
        {
            reported = reported.note(format!(
                "`{name}` is a field or a property, and those are reached with `.` (LR12.2)."
            ));
        }

        // LR20: a block that adds it is the fix, and naming it saves the
        // reader working out which module to import.
        for block in self.blocks_adding(receiver, name) {
            reported = reported.note(format!(
                "`{block}` adds `{name}` to this type. Import it to use it (LR20)."
            ));
        }

        self.diagnostics.push(reported);
    }

    /// The extension blocks anywhere in the program that add `name` to
    /// `receiver` and that this module could import (LR20, LR21.1).
    fn blocks_adding(&self, receiver: &Type, name: &str) -> Vec<String> {
        self.table
            .decls()
            .filter_map(|(module, block, decl)| match decl {
                Decl::Extension { target, methods }
                    if target == receiver
                        && methods.contains_key(name)
                        && self.names.scope(module).exports(block) =>
                {
                    Some(block.to_owned())
                }
                _ => None,
            })
            .collect()
    }

    /// The signature a plain name calls, where the table holds one.
    ///
    /// A callee this stage cannot name a signature for is left alone: a
    /// closure held in a local, or a predeclared name.
    fn declared(&self, name: &str) -> Option<Overloads> {
        // A local holding a function shadows a declaration of the same name.
        if self.shadowed(name) {
            return None;
        }

        let (module, name) = match self.names.scope(self.scope).get(name).map(|b| &b.origin) {
            Some(Origin::Declared { .. }) => (self.scope, name.to_owned()),
            Some(Origin::Imported { module, name }) => (*module, name.clone()),
            _ => return None,
        };

        self.table.overloads(module, &name).cloned()
    }

    /// What `Owner.name(...)` calls: a member of the type `Owner` names, or a
    /// method of the extension block it names (LR12.2, LR42, LR76).
    fn qualified(&mut self, owner: &str, name: &str, span: Span) -> Option<Callee> {
        // A local of that name holds a value, and a value is not a type or a
        // block.
        if self.shadowed(owner) {
            return None;
        }

        // LR15.3: `Enum.Variant(...)` builds a value of the enum, and its
        // payload is checked the way a call checks its arguments.
        if let Some((built, Variant::Tuple(payload))) = self.variant(owner, name) {
            return Some(Callee {
                name: format!("{owner}.{name}"),
                overloads: vec![Signature {
                    asynchronous: false,
                    params: payload
                        .into_iter()
                        .enumerate()
                        .map(|(index, ty)| crate::table::Param {
                            name: index.to_string(),
                            ty,
                            optional: false,
                            variadic: false,
                        })
                        .collect(),
                    result: built,
                    takes_self: false,
                    visibility: None,
                    span,
                }],
                receiver: None,
            });
        }

        // A block is known by the name this module binds it to, and only
        // where it is in scope (LR20).
        if let Some(extension) = self
            .extensions
            .iter()
            .find(|extension| extension.name == owner)
        {
            let overloads = extension.methods.get(name)?.clone();
            let receiver = takes_self(&overloads).then(|| extension.target.clone());
            return Some(Callee {
                name: name.to_owned(),
                overloads,
                receiver,
            });
        }

        let (module, owner) = match self.names.scope(self.scope).get(owner).map(|b| &b.origin) {
            Some(Origin::Declared { .. }) => (self.scope, owner.to_owned()),
            Some(Origin::Imported { module, name }) => (*module, name.clone()),
            _ => return None,
        };

        let overloads = self
            .table
            .structure(module, &owner)?
            .methods
            .get(name)?
            .clone();

        let hidden = overloads
            .iter()
            .all(|signature| signature.visibility == Some(Visibility::Private));
        if hidden {
            self.private(Some(Visibility::Private), module, &owner, name, span);
        }

        let receiver = takes_self(&overloads).then(|| Type::Named {
            module,
            name: owner.clone(),
            args: Vec::new(),
        });

        Some(Callee {
            name: name.to_owned(),
            overloads,
            receiver,
        })
    }

    /// Whether a binding in scope holds `name`, which a declaration of the
    /// same name does not reach past (LR53).
    fn shadowed(&self, name: &str) -> bool {
        self.values
            .iter()
            .rev()
            .any(|scope| scope.contains_key(name))
    }

    /// LR9.1: every parameter without a default takes an argument, and every
    /// argument has its parameter's type.
    fn arguments(&mut self, signature: &Signature, args: &[Argument], held: &[Type], span: Span) {
        let params = &signature.params;
        let lined_up = fit(signature, args);

        for ((argument, slot), held) in args.iter().zip(&lined_up.slots).zip(held) {
            if let Some(index) = slot {
                self.expect_argument(&params[*index].ty, held, argument.value.span);
            }
        }

        if lined_up.counted {
            return;
        }

        let wanted = params.iter().filter(|param| !param.optional).count();
        let given = args.len();

        self.diagnostics.push(Diagnostic::error(
            codes::ARGUMENT_COUNT,
            span,
            format!(
                "this call passes {given} {}, and {} {wanted} {}",
                plural(given, "argument"),
                if params.len() == wanted {
                    "takes"
                } else {
                    "needs at least"
                },
                plural(wanted, "argument"),
            ),
        ));
    }

    /// LR9.1: a `return` gives a value of the declared result.
    fn expect_return(&mut self, wanted: &Type, held: &Type, span: Span) {
        if self.accepts(wanted, held) {
            return;
        }

        self.diagnostics.push(Diagnostic::error(
            codes::RETURN_TYPE,
            span,
            format!(
                "this returns {}, and the function gives `{wanted}`",
                article(held)
            ),
        ));
    }

    fn expect_argument(&mut self, wanted: &Type, held: &Type, span: Span) {
        if self.accepts(wanted, held) {
            return;
        }

        self.diagnostics.push(Diagnostic::error(
            codes::ARGUMENT_TYPE,
            span,
            format!("expected `{wanted}`, found {}", article(held)),
        ));
    }

    fn name(&mut self, name: &str) -> Type {
        // What a condition proved wins over what the declaration said, for
        // as long as the branch that proved it lasts (LR57).
        for scope in self.narrowed.iter().rev() {
            if let Some(ty) = scope.get(name) {
                return ty.clone();
            }
        }

        self.unnarrowed(name)
    }

    /// The type `name` was declared with, with nothing a condition proved
    /// laid over it.
    fn unnarrowed(&self, name: &str) -> Type {
        for scope in self.values.iter().rev() {
            if let Some(ty) = scope.get(name) {
                return ty.clone();
            }
        }
        Type::Unresolved
    }

    fn unary(&mut self, op: UnaryOp, operand: &Expr) -> Type {
        let held = self.expr(operand);

        match op {
            // LR11.4: `not` takes a `bool` and produces one.
            UnaryOp::Not => {
                if !Type::BOOL.accepts(&held) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::CONDITION_NOT_BOOL,
                            operand.span,
                            format!("`not` takes a `bool`, and this is {held}"),
                        )
                        .note("LuaR has no truthiness (LR4.2)."),
                    );
                }
                Type::BOOL
            }
            UnaryOp::Negate | UnaryOp::BitNot => held,
        }
    }

    fn binary(&mut self, op: BinaryOp, op_span: Span, left: &Expr, right: &Expr) -> Type {
        let held_left = self.expr(left);

        // LR11.4, LR57: the right side of `and` runs only where the left
        // held, so it is checked knowing what the left proved.
        let held_right = if matches!(op, BinaryOp::And) {
            let facts = self.facts(left);
            self.narrow(&facts, true);
            let held = self.expr(right);
            self.widen();
            held
        } else {
            self.expr(right)
        };

        match op {
            // LR11.1: `/` is floating-point division, and on two integers it
            // is a mistake with two spellings to suggest.
            BinaryOp::Divide => {
                if is_integer(&held_left) && is_integer(&held_right) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::FLOAT_DIVISION_ON_INTEGERS,
                            op_span,
                            "`/` is not defined for two integers",
                        )
                        .note(
                            "Write `//` for integer division, or convert first, \
                             as in `a as f64 / b as f64` (LR11.1).",
                        ),
                    );
                }
                Type::Primitive(Primitive::F64)
            }
            // LR11.1: `//` truncates toward zero, which is an answer only
            // integers have.
            BinaryOp::IntegerDivide => {
                let known = [&held_left, &held_right]
                    .iter()
                    .all(|held| !matches!(held, Type::Unresolved));

                if known && !(is_integer(&held_left) && is_integer(&held_right)) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::INTEGER_DIVISION_OPERANDS,
                            op_span,
                            format!("`//` is not defined for ({held_left}, {held_right})"),
                        )
                        .note("Write `/` for floating-point division (LR11.1)."),
                    );
                }

                if held_left == held_right {
                    held_left
                } else {
                    Type::Unresolved
                }
            }
            // LR11.4: `and` and `or` take `bool` operands and produce one.
            BinaryOp::And | BinaryOp::Or => {
                for (held, expr) in [(&held_left, left), (&held_right, right)] {
                    if !Type::BOOL.accepts(held) {
                        let spelling = if op == BinaryOp::And { "and" } else { "or" };
                        self.diagnostics.push(
                            Diagnostic::error(
                                codes::CONDITION_NOT_BOOL,
                                expr.span,
                                format!("`{spelling}` takes `bool` operands, and this is {held}"),
                            )
                            .note(
                                "LuaR has no truthiness, and `and` and `or` do not \
                                 return their operands (LR11.4).",
                            ),
                        );
                    }
                }
                Type::BOOL
            }
            BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::Less
            | BinaryOp::LessEqual
            | BinaryOp::Greater
            | BinaryOp::GreaterEqual => Type::BOOL,
            BinaryOp::Concat => Type::STRING,
            // LR8: `??` produces what the left side holds when it is present.
            BinaryOp::Coalesce => match held_left {
                Type::Optional(inner) => *inner,
                _ => Type::Unresolved,
            },
            // Arithmetic on one numeric type produces it. Mixing them needs
            // the promotion rules of LR39, which are not decided here.
            _ => {
                if held_left == held_right {
                    held_left
                } else {
                    Type::Unresolved
                }
            }
        }
    }

    /// Resolves a type written inside a body.
    fn resolve(&mut self, ty: &luar_ast::Type) -> Type {
        self.types.resolve(ty, self.diagnostics)
    }

    /// Reports a value that cannot be what it is declared to be (LR5.1).
    fn expect(&mut self, wanted: &Type, held: &Type, span: Span) {
        if self.accepts(wanted, held) {
            return;
        }

        self.diagnostics.push(Diagnostic::error(
            codes::TYPE_MISMATCH,
            span,
            format!("expected `{wanted}`, found {}", article(held)),
        ));
    }

    fn declare(&mut self, binding: &Binding, held: Type) {
        for name in bound(binding) {
            // A destructured binding takes the types of what it takes apart,
            // which is a shape this stage does not take apart yet (LR5.3).
            let held = match binding {
                Binding::Name(_) => held.clone(),
                _ => Type::Unresolved,
            };
            self.bind(&name, held);
        }
    }

    fn bind(&mut self, name: &str, held: Type) {
        // A name declared again is not the one a condition proved something
        // about (LR53, LR57).
        self.forget(name);
        self.values
            .last_mut()
            .expect("a scope is open")
            .insert(name.to_owned(), held);
    }

    fn push(&mut self) {
        self.values.push(HashMap::new());
    }

    fn pop(&mut self) {
        self.values.pop();
    }

    /// What `condition` proves about the names it tests (LR57).
    ///
    /// Only a plain name is narrowed. A field or an element can be changed by
    /// anything that reaches the value it sits in, so what a check proved
    /// about one does not survive the next statement.
    fn facts(&mut self, condition: &Expr) -> Vec<Narrowing> {
        match &condition.kind {
            // LR57: a nil check settles whether an optional holds anything.
            ExprKind::Binary {
                op: op @ (BinaryOp::Equal | BinaryOp::NotEqual),
                left,
                right,
                ..
            } => {
                let Some(name) = tested_against_nil(left, right) else {
                    return Vec::new();
                };

                let held = self.name(name);
                if !held.is_optional() {
                    return Vec::new();
                }

                let (present, absent) = (held.without_nil(), Type::Primitive(Primitive::Nil));
                let (when_true, when_false) = match op {
                    BinaryOp::NotEqual => (present, absent),
                    _ => (absent, present),
                };

                vec![Narrowing {
                    name: name.to_owned(),
                    when_true,
                    when_false,
                }]
            }
            // LR57: `is` settles which member of a union a value holds.
            ExprKind::TypeTest { value, ty } => {
                let ExprKind::Name(name) = &value.kind else {
                    return Vec::new();
                };

                let held = self.name(name);
                if matches!(held, Type::Unresolved) {
                    return Vec::new();
                }

                // The walk resolved this type already, and reporting it twice
                // would report one mistake twice.
                let mut reported = Vec::new();
                let tested = self.types.resolve(ty, &mut reported);

                vec![Narrowing {
                    name: name.clone(),
                    when_true: tested.clone(),
                    when_false: held.without(&tested),
                }]
            }
            // Both sides hold where `and` does, and the left is what makes
            // the right safe to write (LR11.4).
            ExprKind::Binary {
                op: BinaryOp::And,
                left,
                right,
                ..
            } => {
                let mut facts = self.facts(left);
                self.narrow(&facts, true);
                let rest = self.facts(right);
                self.widen();

                facts.extend(rest);
                facts
            }
            ExprKind::Unary {
                op: UnaryOp::Not,
                operand,
            } => self
                .facts(operand)
                .into_iter()
                .map(|fact| Narrowing {
                    name: fact.name,
                    when_true: fact.when_false,
                    when_false: fact.when_true,
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    /// Opens a scope where `facts` hold, or where they do not.
    fn narrow(&mut self, facts: &[Narrowing], when_true: bool) {
        let mut scope = HashMap::new();
        for fact in facts {
            let held = if when_true {
                &fact.when_true
            } else {
                &fact.when_false
            };
            scope.insert(fact.name.clone(), held.clone());
        }
        self.narrowed.push(scope);
    }

    fn widen(&mut self) {
        self.narrowed.pop();
    }

    /// Drops what was proved about `name`, because the value it holds is no
    /// longer the one that was checked (LR57).
    fn forget(&mut self, name: &str) {
        for scope in &mut self.narrowed {
            scope.remove(name);
        }
    }
}

/// The name a `x == nil` or `x ~= nil` test is about, whichever side the
/// `nil` is written on (LR57).
fn tested_against_nil<'a>(left: &'a Expr, right: &'a Expr) -> Option<&'a str> {
    match (&left.kind, &right.kind) {
        (ExprKind::Name(name), ExprKind::Nil) | (ExprKind::Nil, ExprKind::Name(name)) => Some(name),
        _ => None,
    }
}

/// The type a literal takes when nothing asks for a particular one: `local
/// count = 10` is an `int` (LR7, LR4.3).
fn settle(ty: Type) -> Type {
    match ty {
        Type::IntegerLiteral(_) => Type::Primitive(Primitive::I64),
        Type::FloatLiteral => Type::Primitive(Primitive::F64),
        // A bracket literal with nothing asking for an array is a list
        // (LR13.1).
        Type::SequenceLiteral(element) => Type::Builtin {
            kind: Builtin::List,
            args: vec![settle(*element)],
        },
        other => other,
    }
}

/// What two elements of one literal have in common. Elements of different
/// types need the union rules of LR17.2, so they are left unresolved rather
/// than guessed at.
fn unify(left: Type, right: Type) -> Type {
    if left == right {
        left
    } else {
        Type::Unresolved
    }
}

fn is_integer(ty: &Type) -> bool {
    match ty {
        Type::IntegerLiteral(_) => true,
        Type::Primitive(primitive) => primitive.is_integer(),
        _ => false,
    }
}

/// Reads a type into a sentence. The literal types already name themselves.
fn article(ty: &Type) -> String {
    match ty {
        Type::IntegerLiteral(_) | Type::FloatLiteral | Type::Unresolved => ty.to_string(),
        other => format!("`{other}`"),
    }
}

/// The type of the member called `name`, or unresolved where the type has no
/// such member. A missing member is reported where it is read, not here.
fn field_type(fields: &[Field], name: &str) -> Type {
    fields
        .iter()
        .find(|field| field.name == name)
        .map_or(Type::Unresolved, |field| field.ty.clone())
}

fn plural(count: usize, word: &str) -> String {
    if count == 1 {
        word.to_owned()
    } else {
        format!("{word}s")
    }
}
