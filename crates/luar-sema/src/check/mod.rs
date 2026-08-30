//! Typing every expression, and reporting the programs that are wrong about
//! them (LR4.2, LR5.1, LR7, LR11.1, LR54).

use std::collections::{BTreeMap, HashMap, HashSet};

use luar_ast::{
    Binding, Block, Decorator, Function, InterfaceMember, Item, Member, Module, Param, Property,
    Semantics, Struct, Visibility,
};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::annotations::Resolver;
use crate::facts::Facts;
use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin};
use crate::table::{Decl, Overloads, Signature, Table};
use crate::types::{Builtin, Type};

use calls::written;
use expr::field_type;
use narrow::Place;
use operators::{settle, unify};
use stmt::{assigned, assigned_items};

mod builtins;
mod calls;
mod closures;
mod exhaustive;
mod expr;
mod interfaces;
mod narrow;
mod operators;
mod patterns;
mod stmt;
mod unsafe_ops;

pub use builtins::runtime_symbol;
pub use operators::protocol_of;

/// Checks the types of every module in `graph`, and gives back what it worked
/// out along the way.
#[must_use]
pub fn check(graph: &Graph, names: &Names, table: &Table) -> (Facts, Vec<Diagnostic>) {
    let mut diagnostics = Vec::new();
    let (_, facts) = walk(graph, names, table, &mut diagnostics);
    (facts, diagnostics)
}

/// Works out the result of every function that writes none down (LR7).
pub fn infer_results(graph: &Graph, names: &Names, table: &mut Table) {
    /// Enough rounds for a chain of functions each returning the next, and
    /// few enough that a cycle costs nothing.
    const ROUNDS: usize = 8;

    for _ in 0..ROUNDS {
        let mut ignored = Vec::new();
        let (collected, _) = walk(graph, names, table, &mut ignored);

        let mut changed = false;
        for span in table.inferred() {
            // LR7: several returns agreeing is what the result is.
            let result = collected
                .get(&span)
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .map(settle)
                .reduce(unify)
                .unwrap_or_else(|| Type::Tuple(Vec::new()));

            changed |= table.infer_result(span, &result);
        }

        if !changed {
            return;
        }
    }
}

/// One walk of every module, reporting into `diagnostics` and giving back
/// what each body returns and what the walk worked out.
fn walk(
    graph: &Graph,
    names: &Names,
    table: &Table,
    diagnostics: &mut Vec<Diagnostic>,
) -> (HashMap<Span, Vec<Type>>, Facts) {
    let mut collected = HashMap::new();
    let mut facts = Facts::default();

    for (id, node) in graph.modules() {
        let mut checker = Checker {
            graph,
            names,
            table,
            types: Resolver::new(names, table.kinds(), table.aliases(), id),
            scope: id,
            values: vec![HashMap::new()],
            constants: vec![HashSet::new()],
            unwritten: HashSet::new(),
            loops: Vec::new(),
            unsafely: 0,
            extensions: extensions(names, table, id),
            bodies: Vec::new(),
            collected: HashMap::new(),
            constraints: Vec::new(),
            returns: Vec::new(),
            asynchronously: Vec::new(),
            narrowed: Vec::new(),
            mutations: Vec::new(),
            closures: Vec::new(),
            facts: Facts::default(),
            diagnostics,
        };
        checker.module(&node.ast);
        collected.extend(checker.collected);
        facts.absorb(checker.facts);
    }

    (collected, facts)
}

struct Checker<'a> {
    graph: &'a Graph,
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
    /// Which of them `const` bound, scope for scope alongside `values`
    /// (LR5.2).
    constants: Vec<HashSet<String>>,
    /// Bindings declared with a type and no value, which nothing has written
    /// to yet (LR5.1).
    unwritten: HashSet<String>,
    /// Loops in the current function, outermost first.
    loops: Vec<LoopFlow>,
    /// How many `unsafe` contexts are open around what is being walked
    /// (LR29.2). An `unsafe` function opens one for its whole body.
    unsafely: usize,
    /// The extension blocks this module may reach (LR20).
    extensions: Vec<Extension<'a>>,
    /// The declaration each body being walked belongs to, innermost last. A
    /// closure pushes nothing, because what it returns is its own (LR7).
    bodies: Vec<Option<Span>>,
    /// What each body returns, by the declaration it belongs to (LR7).
    collected: HashMap<Span, Vec<Type>>,
    /// What `where` requires of the type parameters in scope, innermost last
    /// (LR19). It is what gives `T` any members at all inside the body.
    constraints: Vec<HashMap<String, Type>>,
    /// What the function being walked declares it returns, innermost last
    /// (LR9.1). `None` where nothing was written down to check against.
    returns: Vec<Option<Type>>,
    /// Whether each of those bodies is async, which is where `await` may be
    /// written (LR27).
    asynchronously: Vec<bool>,
    /// What conditions have proved about places in scope, innermost last
    /// (LR57). Kept apart from `values` so that a name declared again inside
    /// a branch is a new name rather than the narrowed one.
    narrowed: Vec<HashMap<Place, Type>>,
    /// Names assigned anywhere in each enclosing function body (LR9.8).
    mutations: Vec<HashSet<String>>,
    /// Anonymous functions currently being checked, outermost first.
    closures: Vec<ClosureCaptures>,
    /// What this walk worked out, for lowering to read rather than derive
    /// again.
    facts: Facts,
    diagnostics: &'a mut Vec<Diagnostic>,
}

/// A field or property found on a type, and the declaration it came from.
struct Found {
    module: ModuleId,
    owner: String,
    visibility: Option<Visibility>,
    ty: Type,
}

/// What a condition proves about one place where it holds, and where it does
/// not (LR57).
struct Narrowing {
    place: Place,
    when_true: Type,
    when_false: Type,
}

struct LoopFlow {
    label: Option<String>,
    body_depth: usize,
    repeat_scope: Option<usize>,
    continues: Vec<ContinueFlow>,
}

struct ContinueFlow {
    unwritten: HashSet<String>,
    declared: HashSet<String>,
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
    /// What the receiver bound the type parameters of an extension block to,
    /// ahead of any the call writes (LR20).
    type_args: Vec<Type>,
}

struct ClosureCaptures {
    /// The first value scope belonging to the closure.
    base: usize,
    values: HashMap<String, Type>,
    mutable: HashSet<String>,
    outer_mutations: HashSet<String>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ThreadMarker {
    Send,
    Sync,
}

impl ThreadMarker {
    fn name(self) -> &'static str {
        match self {
            Self::Send => "Send",
            Self::Sync => "Sync",
        }
    }
}

/// How a call lines up with one signature (LR9.1, LR9.4, LR9.5, LR9.6).
struct Fit {
    /// The parameter each argument fills, where it fills one.
    slots: Vec<Option<usize>>,
    /// Whether every parameter needing an argument got one, and none spilled.
    counted: bool,
}

/// An extension block a module can use, under the name that module knows it
/// by, which `as` may have changed (LR20, LR21.1).
struct Extension<'a> {
    name: &'a str,
    type_params: &'a [String],
    target: &'a Type,
    methods: &'a BTreeMap<String, Overloads>,
}

/// The extension blocks in scope in `module`: the ones it declares and the
/// ones it imports by name (LR20).
fn extensions<'a>(names: &'a Names, table: &'a Table, module: ModuleId) -> Vec<Extension<'a>> {
    let mut found = Vec::new();

    for (local, binding) in names.scope(module).names() {
        let decl = match &binding.origin {
            Origin::Declared { .. } => table.get(module, local),
            Origin::Imported { module, name } => table.get(*module, name),
            Origin::Binding { .. } | Origin::Namespace(_) => continue,
        };

        if let Some(Decl::Extension {
            type_params,
            target,
            methods,
        }) = decl
        {
            found.push(Extension {
                name: local,
                type_params,
                target,
                methods,
            });
        }
    }

    found
}

impl Checker<'_> {
    fn module(&mut self, module: &Module) {
        self.mutations.push(assigned_items(&module.items));
        for item in &module.items {
            self.item(item);
        }
        self.mutations.pop();
    }

    fn item(&mut self, item: &Item) {
        match item {
            // A declaration the table holds was resolved when the table was
            // built, so its body is checked against what is recorded there.
            Item::Function(function) => {
                self.reject_finalizers(&function.decorators);
                self.check_intrinsic(function);

                // LR20: a qualified name writes a member of the type it names,
                // so its body reads `self` as that type.
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
                self.body(function, signature.as_ref(), receiver, false);
            }
            Item::Struct(structure) => self.structure(structure),
            Item::Extend(extend) => {
                self.reject_finalizers(&extend.decorators);
                for function in &extend.functions {
                    self.reject_finalizers(&function.decorators);
                }

                let (target, methods) = match self.table.get(self.scope, &extend.name) {
                    Some(Decl::Extension {
                        target, methods, ..
                    }) => (target.clone(), methods.clone()),
                    _ => (Type::Unresolved, BTreeMap::new()),
                };

                // LR65: `Self` in an extension block is the type it extends.
                self.types.enter(&extend.type_params);
                self.types.enter_enclosing(target.clone());

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
                    self.body(function, signature, receiver, false);
                }

                self.types.leave_enclosing();
                self.types.leave();
            }
            // Nothing of these is written outside their own types, which the
            // table already read.
            Item::Enum(enumeration) => self.reject_finalizers(&enumeration.decorators),
            Item::Interface(interface) => {
                self.reject_finalizers(&interface.decorators);
                for member in &interface.members {
                    if let InterfaceMember::Function(function) = member {
                        self.reject_finalizers(&function.decorators);
                    }
                }
            }
            Item::TypeAlias(alias) => self.reject_finalizers(&alias.decorators),
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
        self.reject_finalizers(&structure.decorators);
        if structure.semantics != Semantics::Ref {
            for member in &structure.members {
                if let Member::Function { function, .. } = member {
                    self.reject_finalizers(&function.decorators);
                }
            }
        }

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
            if let Some(marker) = self.thread_marker(resolved) {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::EXPLICIT_THREAD_MARKER,
                        written.span,
                        format!("`{}` is derived by the compiler", marker.name()),
                    )
                    .note(
                        "User source may name `Send` and `Sync` as constraints, not in an `implements` clause (LR28).",
                    ),
                );
                continue;
            }
            self.conforms(&claimed, resolved, written.span);
        }

        // LR65: `self` in a member is the type the member is declared in.
        let receiver = self.receiver(&structure.name);

        self.types.enter(&structure.type_params);
        // LR65: `Self` is that same type, written down.
        self.types.enter_enclosing(receiver.clone());

        if structure.semantics == Semantics::Ref {
            self.finalizers(structure);
        }

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
                    let finalizer =
                        structure.semantics == Semantics::Ref && instance_finalizer(function);
                    let overloads = (!finalizer)
                        .then(|| {
                            function
                                .name
                                .last()
                                .and_then(|name| declared.methods.get(name))
                        })
                        .flatten();
                    let signature = written(overloads, function.span).cloned();
                    self.body(
                        function,
                        signature.as_ref(),
                        Some(receiver.clone()),
                        finalizer,
                    );
                }
                Member::Property(property) => {
                    let held = field_type(&declared.properties, &property.name);
                    self.property(property, held, receiver.clone());
                }
            }
        }

        self.types.leave_enclosing();
        self.types.leave();
    }

    fn reject_finalizers(&mut self, decorators: &[Decorator]) {
        for decorator in finalizers(decorators) {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::FINALIZER_TARGET,
                    decorator.span,
                    "this declaration cannot be a finalizer",
                )
                .note("`@finalizer` applies to an instance function in a `ref struct` (LR51)."),
            );
        }
    }

    fn finalizers(&mut self, structure: &Struct) {
        let mut first = None;

        for function in structure.members.iter().filter_map(|member| match member {
            Member::Function { function, .. } => Some(function),
            Member::Field(_) | Member::Property(_) => None,
        }) {
            let decorators: Vec<&Decorator> = finalizers(&function.decorators).collect();
            for decorator in &decorators {
                if let Some(first) = first {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::DUPLICATE_FINALIZER,
                            decorator.span,
                            format!("`{}` already has a finalizer", structure.name),
                        )
                        .label(first, "first declared here"),
                    );
                } else {
                    first = Some(decorator.span);
                }
            }

            let Some(decorator) = decorators.first() else {
                continue;
            };

            if !instance_finalizer(function) {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::FINALIZER_TARGET,
                        decorator.span,
                        "this is not an instance function",
                    )
                    .note("A finalizer is an instance function in a `ref struct` (LR51)."),
                );
                continue;
            }

            let result_is_unit = function.result.as_ref().is_none_or(
                |result| matches!(self.resolve(result), Type::Tuple(items) if items.is_empty()),
            );
            if function.asynchronous
                || !function.type_params.is_empty()
                || !function.constraints.is_empty()
                || function.params.len() != 1
                || !result_is_unit
            {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::FINALIZER_SIGNATURE,
                        decorator.span,
                        "this function cannot be used as a finalizer",
                    )
                    .note(
                        "A finalizer takes only `self`, returns `()`, and is not async or generic (LR51).",
                    ),
                );
            }
        }
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
        self.asynchronously.push(false);
        self.mutations.push(assigned(&property.get));
        self.block(&property.get);
        self.mutations.pop();
        self.asynchronously.pop();
        self.returns.pop();
        self.pop();

        if let Some(setter) = &property.set {
            self.push();
            self.bind("self", receiver);
            self.bind(&setter.param, held);
            self.returns.push(Some(Type::Tuple(Vec::new())));
            self.asynchronously.push(false);
            self.mutations.push(assigned(&setter.body));
            self.block(&setter.body);
            self.mutations.pop();
            self.asynchronously.pop();
            self.returns.pop();
            self.pop();
        }
    }

    /// Checks a function body against its signature.
    fn body(
        &mut self,
        function: &Function,
        signature: Option<&Signature>,
        receiver: Option<Type>,
        finalizer: bool,
    ) {
        self.types.enter(&function.type_params);
        self.push();

        if let Some(receiver) = receiver {
            self.bind("self", receiver);
        }

        // LR65: `self` is written like a parameter, but its type is the
        // receiver bound above rather than anything the parameter list says.
        let params = match (finalizer, signature) {
            (true, _) => function.params.get(1..).unwrap_or_default(),
            (false, Some(signature)) if signature.takes_self => {
                function.params.get(1..).unwrap_or_default()
            }
            (false, _) => function.params.as_slice(),
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

        let returns = match (finalizer, signature) {
            (true, _) => Some(Type::Tuple(Vec::new())),
            (false, Some(signature)) => Some(signature.result.clone()),
            (false, None) => function.result.as_ref().map(|result| self.resolve(result)),
        };

        let constraints = match signature {
            Some(signature) => signature.constraints.iter().cloned().collect(),
            None => function
                .constraints
                .iter()
                .map(|constraint| {
                    (
                        constraint.parameter.clone(),
                        self.resolve(&constraint.bound),
                    )
                })
                .collect(),
        };

        // LR29.2: an `unsafe` function is one long unsafe context, which is
        // what lets a foreign call be written plainly inside it (LR46).
        let unsafely = usize::from(function.unsafe_);
        self.unsafely += unsafely;

        self.constraints.push(constraints);
        self.returns.push(returns);
        self.asynchronously.push(function.asynchronous);
        self.bodies.push(Some(function.span));
        self.mutations
            .push(function.body.as_ref().map_or_else(HashSet::new, assigned));
        if let Some(body) = &function.body {
            for stmt in &body.stmts {
                self.stmt(stmt);
            }
        }
        self.mutations.pop();
        self.bodies.pop();
        self.asynchronously.pop();
        self.returns.pop();
        self.constraints.pop();
        self.unsafely -= unsafely;

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

        let held = if param.variadic {
            Type::Builtin {
                kind: Builtin::FrozenList,
                args: vec![declared],
            }
        } else {
            declared
        };
        self.declare(&param.binding, held, param.span);
    }

    fn block(&mut self, block: &Block) {
        self.push();
        for stmt in &block.stmts {
            self.stmt(stmt);
        }
        self.pop();
    }

    fn declare(&mut self, binding: &Binding, held: Type, span: Span) {
        match binding {
            Binding::Name(name) => self.bind(name, held),
            Binding::Record(fields) => {
                if !self.record_shape(&held) {
                    self.invalid_destructure(span, &held);
                    self.bind_unresolved(binding);
                    return;
                }

                for field in fields {
                    let name = field.bound_as.as_ref().unwrap_or(&field.field);
                    let Some((ty, owner)) = self.destructured_field(&held, &field.field) else {
                        if !matches!(held, Type::Unresolved) {
                            self.diagnostics.push(
                                Diagnostic::error(
                                    codes::INVALID_DESTRUCTURE,
                                    field.span,
                                    format!("`{held}` has no field `{}`", field.field),
                                )
                                .note("A record binding names fields in its statically known shape (LR5.3)."),
                            );
                        }
                        self.bind(name, Type::Unresolved);
                        continue;
                    };

                    if let Some((visibility, module, declared)) = owner {
                        self.private(visibility, module, &declared, &field.field, field.span);
                    }
                    self.bind(name, ty);
                }
            }
            Binding::Tuple(bindings) => {
                let Type::Tuple(members) = &held else {
                    if !matches!(held, Type::Unresolved) {
                        self.invalid_destructure(span, &held);
                    }
                    self.bind_unresolved(binding);
                    return;
                };

                if bindings.len() != members.len() {
                    self.invalid_destructure(span, &held);
                    self.bind_unresolved(binding);
                    return;
                }

                for (binding, member) in bindings.iter().zip(members) {
                    self.declare(binding, member.clone(), span);
                }
            }
            Binding::Error => {}
        }
    }

    fn record_shape(&self, held: &Type) -> bool {
        match held {
            Type::Record(_) | Type::Unresolved => true,
            Type::Named { module, name, .. } => {
                matches!(self.table.get(*module, name), Some(Decl::Struct(_)))
            }
            _ => false,
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
        self.constants.push(HashSet::new());
        self.types.push_constants();
    }

    fn pop(&mut self) {
        self.values.pop();
        self.constants.pop();
        self.types.pop_constants();
    }
}

fn finalizers(decorators: &[Decorator]) -> impl Iterator<Item = &Decorator> {
    decorators
        .iter()
        .filter(|decorator| decorator.name == "finalizer")
}

fn instance_finalizer(function: &Function) -> bool {
    finalizers(&function.decorators).next().is_some()
        && !function.static_
        && matches!(
            function.params.first().map(|param| &param.binding),
            Some(Binding::Name(name)) if name == "self"
        )
}
