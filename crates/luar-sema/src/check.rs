//! Typing every expression, and reporting the programs that are wrong about
//! them (LR4.2, LR5.1, LR7, LR11.1, LR54).

use std::collections::{BTreeMap, HashMap, HashSet};

use luar_ast::{
    Argument, ArmBody, BinaryOp, Binding, Block, Decorator, Expr, ExprKind, FieldInit, Function,
    FunctionBody, InterfaceMember, InterpolationPart, Item, MapKey, MatchArm, Member, Module,
    Param, Pattern, PatternKind, Payload, Property, Semantics, Stmt, StmtKind, Struct, UnaryOp,
    Visibility,
};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::aliases::substitute;
use crate::annotations::Resolver;
use crate::facts::{CollectionMutation, Facts, Intrinsic, Overflow, OverflowMethod};
use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin, bound};
use crate::table::{Decl, Field, Overloads, SELF, Signature, Table, Variant};
use crate::types::{Builtin, Primitive, Type};

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
    /// What conditions have proved about names in scope, innermost last
    /// (LR57). Kept apart from `values` so that a name declared again inside
    /// a branch is a new name rather than the narrowed one.
    narrowed: Vec<HashMap<String, Type>>,
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

type DestructuredField = (Type, Option<(Option<Visibility>, ModuleId, String)>);

/// What a condition proves about one name where it holds, and where it does
/// not (LR57).
struct Narrowing {
    name: String,
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

/// What one case of a match covers (LR16.4).
enum Covers {
    /// Every value, which is what a wildcard and a bare binding match.
    Anything,
    /// One case of a closed type, named as a pattern writes it.
    Case(String),
}

/// What `pattern` covers, where that is something this stage can name.
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
                let fits = index < params.len() || (variadic && !params.is_empty());
                fits.then_some(index.min(params.len().saturating_sub(1)))
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

/// Reads what a type parameter must be by lining a declared type up with the
/// type of what was passed for it (LR19).
fn infer(params: &[String], wanted: &Type, held: &Type, bound: &mut BTreeMap<String, Type>) {
    match (wanted, held) {
        (Type::Parameter(name), held) if params.iter().any(|param| param == name) => {
            if !matches!(held, Type::Unresolved) {
                bound
                    .entry(name.clone())
                    .or_insert_with(|| settle(held.clone()));
            }
        }
        (Type::Optional(wanted), Type::Optional(held)) => infer(params, wanted, held, bound),
        (Type::Array(wanted), Type::Array(held)) => infer(params, wanted, held, bound),
        (Type::Array(wanted), Type::SequenceLiteral(held)) => infer(params, wanted, held, bound),
        (Type::Pointer { target: wanted, .. }, Type::Pointer { target: held, .. }) => {
            infer(params, wanted, held, bound);
        }
        (
            Type::Builtin { kind, args },
            Type::Builtin {
                kind: held_kind,
                args: had,
            },
        ) if kind == held_kind => {
            for (wanted, held) in args.iter().zip(had) {
                infer(params, wanted, held, bound);
            }
        }
        (
            Type::Named { name, args, .. },
            Type::Named {
                name: had_name,
                args: had,
                ..
            },
        ) if name == had_name => {
            for (wanted, held) in args.iter().zip(had) {
                infer(params, wanted, held, bound);
            }
        }
        (Type::Tuple(wanted), Type::Tuple(held)) => {
            for (wanted, held) in wanted.iter().zip(held) {
                infer(params, wanted, held, bound);
            }
        }
        (
            Type::Function {
                params: wanted,
                result,
                ..
            },
            Type::Function {
                params: had,
                result: had_result,
                ..
            },
        ) => {
            for (wanted, held) in wanted.iter().zip(had) {
                infer(params, wanted, held, bound);
            }
            infer(params, result, had_result, bound);
        }
        _ => {}
    }
}

/// Overloads with the type arguments of the receiver put where the type
/// declares its parameters (LR19).
fn filled(overloads: &[Signature], params: &[String], args: &[Type]) -> Overloads {
    overloads
        .iter()
        .map(|signature| Signature {
            params: signature
                .params
                .iter()
                .map(|param| crate::table::Param {
                    ty: substitute(&param.ty, params, args),
                    ..param.clone()
                })
                .collect(),
            result: substitute(&signature.result, params, args),
            ..signature.clone()
        })
        .collect()
}

/// One signature an interface requires, with `Self` standing for the type
/// being checked against it (LR65).
fn against(required: &Signature, implementor: &Type) -> Signature {
    filled(
        std::slice::from_ref(required),
        &[SELF.to_owned()],
        std::slice::from_ref(implementor),
    )
    .pop()
    .unwrap_or_else(|| required.clone())
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
                    Some(Decl::Extension { target, methods }) => (target.clone(), methods.clone()),
                    _ => (Type::Unresolved, BTreeMap::new()),
                };

                // LR65: `Self` in an extension block is the type it extends.
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

        self.declare(&param.binding, declared, param.span);
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
                let initialized = self.expr(value);
                let held = match ty {
                    Some(ty) => {
                        let declared = self.resolve(ty);
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
                // yields what the iterator protocol says (LR35), which is
                // not resolved here.
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
                        _ => None,
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
                    Some(value) => self.expr(value),
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

    /// LR16.4: a match over a closed type covers every value it can hold, and
    /// a case an earlier one already covers never runs.
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

    /// LR10.4: a range written in place yields its bounds' type. LR39: a
    /// literal bound takes the other bound's type.
    fn range_element(&mut self, start: &Expr, end: &Expr) -> Type {
        let start = self.expr(start);
        let end = self.expr(end);
        match (start, end) {
            (Type::IntegerLiteral(_), other) | (other, Type::IntegerLiteral(_)) => settle(other),
            (start, end) => settle(unify(start, end)),
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

    /// The type of an expression, recorded for the stages after this one.
    fn expr(&mut self, expr: &Expr) -> Type {
        let ty = self.expr_type(expr);
        self.facts.record_type(expr.span, ty.clone());
        ty
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

                self.name(name)
            }
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
                let written: Vec<Type> = type_args.iter().map(|ty| self.resolve(ty)).collect();
                let receiver = self.expr(callee);
                self.call(
                    callee,
                    method.as_deref(),
                    &receiver,
                    &written,
                    args,
                    expr.span,
                )
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
                let held = self.expr(inner);
                self.propagated(&held, expr.span)
            }
            ExprKind::Await(inner) => {
                let held = self.expr(inner);
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
                self.resolve(ty);
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
            ExprKind::Function {
                asynchronous,
                params,
                result,
                body,
            } => {
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
                self.asynchronously.push(*asynchronous);
                self.bodies.push(None);

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

                Type::Function {
                    asynchronous: *asynchronous,
                    sendable,
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
    fn member(&mut self, held: &Type, name: &str, span: Span) -> Type {
        if !self.settled(held, name, span) {
            return Type::Unresolved;
        }

        if let Some(found) = self.stored(held, name) {
            self.private(found.visibility, found.module, &found.owner, name, span);
            return found.ty;
        }

        // LR13: `length` is how many elements a collection holds.
        if is_collection(held) && name == "length" {
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
            .and_then(|overloads| {
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
                let held = self.methods_of(claimed, member).is_some_and(|had| {
                    let required = against(required, claimed);
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
    fn accepts(&self, wanted: &Type, held: &Type) -> bool {
        if let Some(marker) = self.thread_marker(wanted) {
            return self.has_thread_marker(held, marker);
        }
        wanted.accepts(held) || self.satisfies(wanted, held)
    }

    /// Whether `held` satisfies the interface `wanted` (LR18).
    fn satisfies(&self, wanted: &Type, held: &Type) -> bool {
        if let Some(marker) = self.thread_marker(wanted) {
            return self.has_thread_marker(held, marker);
        }

        let Type::Named { module, name, .. } = wanted else {
            return false;
        };
        let Some(Decl::Interface(interface)) = self.table.get(*module, name) else {
            return false;
        };

        // A structural interface is satisfied by any type with the members,
        // declared or not.
        if interface.structural {
            return interface.methods.iter().all(|(member, required)| {
                required.iter().all(|required| {
                    self.methods_of(held, member).is_some_and(|had| {
                        let required = against(required, held);
                        had.iter().any(|had| same_signature(had, &required))
                    })
                })
            });
        }

        self.implements(held, wanted)
    }

    fn thread_marker(&self, ty: &Type) -> Option<ThreadMarker> {
        let Type::Named { module, name, .. } = ty else {
            return None;
        };
        if self.graph.module(*module).path != std::path::Path::new("std/thread") {
            return None;
        }

        match name.as_str() {
            "Send" => Some(ThreadMarker::Send),
            "Sync" => Some(ThreadMarker::Sync),
            _ => None,
        }
    }

    fn has_thread_marker(&self, ty: &Type, marker: ThreadMarker) -> bool {
        self.has_thread_marker_inner(ty, marker, &mut HashSet::new())
    }

    fn has_thread_marker_inner(
        &self,
        ty: &Type,
        marker: ThreadMarker,
        visiting: &mut HashSet<(ModuleId, String)>,
    ) -> bool {
        match ty {
            Type::Unresolved | Type::Primitive(Primitive::Never) => true,
            Type::Primitive(Primitive::Any | Primitive::Unknown) => false,
            Type::Primitive(_) | Type::IntegerLiteral(_) | Type::FloatLiteral => true,
            Type::Builtin {
                kind:
                    Builtin::Result | Builtin::FrozenList | Builtin::FrozenMap | Builtin::FrozenSet,
                args,
            } => args
                .iter()
                .all(|arg| self.has_thread_marker_inner(arg, marker, visiting)),
            Type::Builtin { .. } | Type::SequenceLiteral(_) | Type::Pointer { .. } => false,
            Type::Optional(inner) | Type::Array(inner) => {
                self.has_thread_marker_inner(inner, marker, visiting)
            }
            Type::Union(members) | Type::Tuple(members) => members
                .iter()
                .all(|member| self.has_thread_marker_inner(member, marker, visiting)),
            Type::Intersection(members) => members
                .iter()
                .any(|member| self.has_thread_marker_inner(member, marker, visiting)),
            Type::Function { sendable, .. } => marker == ThreadMarker::Send && *sendable,
            Type::Parameter(parameter) => self
                .constraints
                .iter()
                .rev()
                .find_map(|scope| scope.get(parameter))
                .is_some_and(|bound| self.has_thread_marker_inner(bound, marker, visiting)),
            Type::Named { module, name, args } => {
                if self.thread_marker(ty) == Some(marker) {
                    return true;
                }

                let key = (*module, name.clone());
                if !visiting.insert(key.clone()) {
                    return true;
                }

                let derived = match self.table.get(*module, name) {
                    Some(Decl::Struct(structure)) if structure.semantics != Semantics::Ref => {
                        structure.fields.iter().all(|field| {
                            let held = substitute(&field.ty, &structure.type_params, args);
                            self.has_thread_marker_inner(&held, marker, visiting)
                        })
                    }
                    Some(Decl::Enum(enumeration)) => enumeration.variants.values().all(|variant| {
                        let fields: Vec<&Type> = match variant {
                            Variant::Unit => Vec::new(),
                            Variant::Tuple(types) => types.iter().collect(),
                            Variant::Record(fields) => {
                                fields.iter().map(|field| &field.ty).collect()
                            }
                        };
                        fields.into_iter().all(|field| {
                            let held = substitute(field, &enumeration.type_params, args);
                            self.has_thread_marker_inner(&held, marker, visiting)
                        })
                    }),
                    _ => false,
                };

                visiting.remove(&key);
                derived
            }
            Type::Record(_) => false,
        }
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
                Decl::Struct(structure) if !structure.expands => Some(declared.clone()),
                Decl::Interface(interface) if !interface.expands => Some(declared.clone()),
                _ => None,
            },
            Type::Builtin {
                kind:
                    Builtin::List
                    | Builtin::Map
                    | Builtin::Set
                    | Builtin::FrozenList
                    | Builtin::FrozenMap
                    | Builtin::FrozenSet,
                ..
            } => Some(held.to_string()),
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
    fn stored(&self, held: &Type, name: &str) -> Option<Found> {
        if let Type::Intersection(parts) = held {
            return parts.iter().find_map(|part| self.stored(part, name));
        }

        let Type::Named {
            module,
            name: declared,
            args,
        } = held
        else {
            return None;
        };

        let (params, field) = match self.table.get(*module, declared)? {
            Decl::Struct(structure) => (
                &structure.type_params,
                structure
                    .fields
                    .iter()
                    .chain(&structure.properties)
                    .find(|field| field.name == name),
            ),
            // An interface requires properties of its own (LR18).
            Decl::Interface(interface) => (
                &interface.type_params,
                interface
                    .properties
                    .iter()
                    .find(|property| property.name == name),
            ),
            _ => return None,
        };
        let field = field?;

        Some(Found {
            module: *module,
            owner: declared.clone(),
            visibility: field.visibility,
            // LR19: a member of `Box<int>` reads as `int`, not as `T`.
            ty: substitute(&field.ty, params, args),
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

        let args: Vec<Type> = params
            .iter()
            .map(|param| bound.get(param).cloned().unwrap_or(Type::Unresolved))
            .collect();

        for field in &mut fields {
            field.ty = substitute(&field.ty, &params, &args);
        }

        self.initializers(&name, module, &fields, written, values, span);

        Type::Named { module, name, args }
    }

    /// The enum variant `owner.name` names, and the enum it builds (LR15.3).
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
    fn call(
        &mut self,
        callee: &Expr,
        method: Option<&str>,
        receiver: &Type,
        written: &[Type],
        args: &[Argument],
        span: Span,
    ) -> Type {
        if result_variant(callee).is_some() && !self.shadowed("Result") && written.len() != 2 {
            for argument in args {
                self.expr(&argument.value);
            }
            return Type::Unresolved;
        }

        let intrinsic = method
            .is_none()
            .then(|| self.predeclared_intrinsic(callee))
            .flatten();
        let freezes = method.is_some_and(|name| frozen_method(receiver, name, span).is_some());
        let checked_index =
            method.is_some_and(|name| checked_index_method(receiver, name, span).is_some());
        let set_contains =
            method.is_some_and(|name| set_contains_method(receiver, name, span).is_some());
        let collection_mutation = method.and_then(|name| {
            collection_mutation_method(receiver, name, span).map(|(mutation, _)| mutation)
        });
        let overflow =
            method.and_then(|name| overflow_method(receiver, name, span).map(|(method, _)| method));
        let resolved = self.signature_of(callee, method, receiver, span);

        // The arguments are expressions whoever is being called, and whatever
        // is wrong inside one is wrong before any overload is picked.
        let held: Vec<Type> = args
            .iter()
            .map(|argument| self.expr(&argument.value))
            .collect();

        // LR32: `identical` takes only values with observable identity.
        if self.is_identical(callee) {
            for (argument, held) in args.iter().zip(&held) {
                let held = settle(held.clone());
                if !self.has_identity(&held) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::IDENTITY_REQUIRED,
                            argument.value.span,
                            format!("`identical` cannot take {}", article(&held)),
                        )
                        .note(
                            "Identity is observable on reference types, closures, interface values, and reference-backed collections (LR32).",
                        ),
                    );
                }
            }
        }

        let Some(resolved) = resolved else {
            return Type::Unresolved;
        };

        // LR12.2: naming the type writes the call out in full, so `self` is an
        // ordinary first argument and is counted and checked as one.
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

        // LR29.2, LR46: an `unsafe` function makes a promise the compiler
        // cannot check, so the call site says out loud that it is keeping it.
        if signature.unsafe_ && self.unsafely == 0 {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::UNSAFE_REQUIRED,
                    span,
                    format!("`{}` is `unsafe`, and this call is not", resolved.name),
                )
                .note("Write it inside an `unsafe` block (LR29.2)."),
            );
        }

        self.facts.record_call(span, signature.span);
        if let Some(intrinsic) = intrinsic {
            self.facts.record_intrinsic(span, intrinsic);
        }
        if freezes {
            self.facts.record_freeze(span);
        }
        if checked_index {
            self.facts.record_checked_index(span);
        }
        if set_contains {
            self.facts.record_set_contains(span);
        }
        if let Some(mutation) = collection_mutation {
            self.facts.record_collection_mutation(span, mutation);
        }
        if let Some(overflow) = overflow {
            self.facts.record_overflow_method(span, overflow);
        }

        // LR19: a generic call takes its type arguments from what it writes
        // down, and works out the rest from what it passes.
        let signature = self.specialize(signature, written, &held, span);

        self.arguments(&signature, args, &held, span);

        // LR27: calling an async function produces a task, and `await` is
        // what takes the result out of it.
        if signature.asynchronous {
            return Type::Builtin {
                kind: Builtin::Task,
                args: vec![settle(signature.result)],
            };
        }
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

    /// One call of a generic signature, with its type parameters worked out
    /// (LR19).
    fn specialize(
        &mut self,
        signature: Signature,
        written: &[Type],
        held: &[Type],
        span: Span,
    ) -> Signature {
        if signature.type_params.is_empty() {
            return signature;
        }

        let mut bound: BTreeMap<String, Type> = signature
            .type_params
            .iter()
            .cloned()
            .zip(written.iter().cloned())
            .collect();

        for (param, held) in signature.params.iter().zip(held) {
            infer(&signature.type_params, &param.ty, held, &mut bound);
        }

        let args: Vec<Type> = signature
            .type_params
            .iter()
            .map(|param| bound.get(param).cloned().unwrap_or(Type::Unresolved))
            .collect();

        // LR19: what fills each parameter is worked out here, and nowhere else
        // knows it.
        self.facts.record_type_args(span, args.clone());

        // LR19: `where` is a promise the call has to keep.
        for (parameter, wanted) in &signature.constraints {
            let Some(index) = signature
                .type_params
                .iter()
                .position(|param| param == parameter)
            else {
                continue;
            };

            let filling = &args[index];
            if matches!(filling, Type::Unresolved) || self.accepts(wanted, filling) {
                continue;
            }

            if let Some(marker) = self.thread_marker(wanted) {
                let use_ = match marker {
                    ThreadMarker::Send => "crosses into another thread",
                    ThreadMarker::Sync => "is shared between threads",
                };
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::THREAD_MARKER_REQUIRED,
                        span,
                        format!("`{filling}` is not `{}`", marker.name()),
                    )
                    .note(format!(
                        "A value that {use_} must be `{}` (LR28).",
                        marker.name()
                    )),
                );
            } else {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::CONSTRAINT_NOT_SATISFIED,
                        span,
                        format!("`{parameter}` is `{filling}` here, and that is not a `{wanted}`"),
                    )
                    .note(format!(
                        "`where {parameter}: {wanted}` is what this call has to meet (LR19)."
                    )),
                );
            }
        }

        Signature {
            params: signature
                .params
                .iter()
                .map(|param| crate::table::Param {
                    ty: substitute(&param.ty, &signature.type_params, &args),
                    ..param.clone()
                })
                .collect(),
            result: substitute(&signature.result, &signature.type_params, &args),
            type_params: Vec::new(),
            constraints: Vec::new(),
            ..signature
        }
    }

    /// LR40: a call resolves to exactly one overload.
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

        // Nothing matching means every overload is worth naming; more than one
        // means only the ones that fit are.
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

        if let Some(intrinsic) = self.predeclared_intrinsic(callee) {
            return Some(Callee {
                name: intrinsic.name().to_owned(),
                overloads: vec![intrinsic_signature(intrinsic, span)],
                receiver: None,
            });
        }

        match &callee.kind {
            ExprKind::Name(name) => {
                let overloads = self.declared(name)?;
                Some(Callee {
                    name: name.clone(),
                    overloads,
                    receiver: None,
                })
            }
            // LR12.2, LR42, LR76: `Owner.name(...)` is a method call written
            // out, a static, or a call naming the extension block it means.
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

        let found = self.find_method(receiver, name, span);
        if found.is_none() {
            self.no_such_method(receiver, name, span);
        }
        found
    }

    /// The same search, reporting nothing where no method has the name. An
    /// operator says for itself what it was looking for (LR36).
    fn find_method(&mut self, receiver: &Type, name: &str, span: Span) -> Option<Overloads> {
        let found = self.lookup_method(receiver, name, span)?;

        // LR65: `Self` in what an interface requires is the type that reached
        // the method, which for a constrained parameter is the parameter.
        Some(filled(
            &found,
            &[SELF.to_owned()],
            std::slice::from_ref(receiver),
        ))
    }

    fn lookup_method(&mut self, receiver: &Type, name: &str, span: Span) -> Option<Overloads> {
        // LR19: inside the body, a type parameter has whatever `where` says it
        // has, and nothing else is known about it.
        if let Type::Parameter(parameter) = receiver {
            let bound = self
                .constraints
                .iter()
                .rev()
                .find_map(|scope| scope.get(parameter))
                .cloned();

            return match bound {
                // Not `find_method`, so that `Self` is still standing when the
                // caller fills it with the parameter rather than its bound.
                Some(bound) => self.lookup_method(&bound, name, span),
                None => None,
            };
        }

        if let Some(signature) = unsafe_memory_method(receiver, name, span) {
            return Some(vec![signature]);
        }
        if let Some(signature) = frozen_method(receiver, name, span) {
            return Some(vec![signature]);
        }
        if let Some(signature) = checked_index_method(receiver, name, span) {
            return Some(vec![signature]);
        }
        if let Some(signature) = set_contains_method(receiver, name, span) {
            return Some(vec![signature]);
        }
        if let Some((_, signature)) = collection_mutation_method(receiver, name, span) {
            return Some(vec![signature]);
        }
        if let Some((_, signature)) = overflow_method(receiver, name, span) {
            return Some(vec![signature]);
        }

        if let Type::Named {
            module,
            name: declared,
            args,
        } = receiver
        {
            match self.table.get(*module, declared) {
                // An inherent method wins over any extension offering the same
                // name, so adding one shadows the extension rather than
                // changing what a call already meant.
                Some(Decl::Struct(structure)) => {
                    if let Some(overloads) = structure
                        .methods
                        .get(name)
                        .map(|overloads| filled(overloads, &structure.type_params, args))
                    {
                        // Where every overload is private, no call from
                        // outside can reach any of them (LR44).
                        let hidden = overloads
                            .iter()
                            .all(|signature| signature.visibility == Some(Visibility::Private));
                        if hidden {
                            self.private(Some(Visibility::Private), *module, declared, name, span);
                        }

                        // LR42: a static has no receiver to be called through,
                        // so it is reached through its type.
                        if !takes_self(&overloads) {
                            self.diagnostics.push(
                                Diagnostic::error(
                                    codes::STATIC_THROUGH_INSTANCE,
                                    span,
                                    format!("`{name}` is static, and takes no receiver"),
                                )
                                .note(format!(
                                    "Call it through the type, as in `{declared}.{name}()` (LR42)."
                                )),
                            );
                        }

                        return Some(overloads);
                    }
                }
                // LR75: an enum declares no members of its own, and what
                // `@derive` wrote out is reached the same way as any other.
                Some(Decl::Enum(enumeration)) => {
                    if let Some(overloads) = enumeration
                        .methods
                        .get(name)
                        .map(|overloads| filled(overloads, &enumeration.type_params, args))
                    {
                        return Some(overloads);
                    }
                }
                // A value of interface type dispatches over what the interface
                // requires (LR18.1).
                Some(Decl::Interface(interface)) => {
                    if let Some(overloads) = interface
                        .methods
                        .get(name)
                        .map(|overloads| filled(overloads, &interface.type_params, args))
                    {
                        return Some(overloads);
                    }
                }
                _ => {}
            }
        }

        self.extension(receiver, name, span)
    }

    /// Reports a method nothing offers, where every place one could come from
    /// is known (LR76).
    fn no_such_method(&mut self, receiver: &Type, name: &str, span: Span) {
        if unavailable_unsafe_memory_method(receiver, name) {
            self.diagnostics.push(Diagnostic::error(
                codes::NO_SUCH_METHOD,
                span,
                format!("`{receiver}` has no method `{name}`"),
            ));
            return;
        }
        if matches!(receiver, Type::Builtin { .. }) {
            self.diagnostics.push(Diagnostic::error(
                codes::NO_SUCH_METHOD,
                span,
                format!("`{receiver}` has no method `{name}`"),
            ));
            return;
        }

        let Type::Named {
            module,
            name: declared,
            ..
        } = receiver
        else {
            return;
        };

        let known = match self.table.get(*module, declared) {
            Some(Decl::Struct(structure)) => !structure.expands,
            Some(Decl::Interface(interface)) => !interface.expands,
            Some(Decl::Enum(enumeration)) => !enumeration.expands,
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

    fn predeclared_intrinsic(&self, callee: &Expr) -> Option<Intrinsic> {
        match &callee.kind {
            ExprKind::Name(name) if !self.shadowed(name) && self.declared(name).is_none() => {
                match name.as_str() {
                    "assert" => Some(Intrinsic::Assert),
                    "debugAssert" => Some(Intrinsic::DebugAssert),
                    "panic" => Some(Intrinsic::Panic),
                    _ => None,
                }
            }
            ExprKind::Field {
                receiver,
                name,
                optional: false,
            } if name == "new" => {
                let ExprKind::Name(owner) = &receiver.kind else {
                    return None;
                };
                if self.shadowed(owner) || self.names.scope(self.scope).get(owner).is_some() {
                    return None;
                }
                match owner.as_str() {
                    "List" => Some(Intrinsic::ListNew),
                    "Map" => Some(Intrinsic::MapNew),
                    "Set" => Some(Intrinsic::SetNew),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn is_identical(&self, callee: &Expr) -> bool {
        let ExprKind::Name(name) = &callee.kind else {
            return false;
        };
        if self.shadowed(name) {
            return false;
        }
        let Some(Origin::Imported { module, name }) = self
            .names
            .scope(self.scope)
            .get(name)
            .map(|binding| &binding.origin)
        else {
            return false;
        };

        name == "identical" && self.graph.module(*module).path == std::path::Path::new("std/mem")
    }

    fn has_identity(&self, ty: &Type) -> bool {
        match ty {
            Type::Unresolved | Type::Primitive(Primitive::Any | Primitive::Never) => true,
            Type::Builtin {
                kind:
                    Builtin::List
                    | Builtin::Map
                    | Builtin::Set
                    | Builtin::FrozenList
                    | Builtin::FrozenMap
                    | Builtin::FrozenSet,
                ..
            }
            | Type::Function { .. } => true,
            Type::Named { module, name, .. } => {
                matches!(
                    self.table.get(*module, name),
                    Some(Decl::Struct(structure)) if structure.semantics == Semantics::Ref
                ) || matches!(self.table.get(*module, name), Some(Decl::Interface(_)))
            }
            Type::Union(members) | Type::Intersection(members) => {
                !members.is_empty() && members.iter().all(|member| self.has_identity(member))
            }
            _ => false,
        }
    }

    /// What `Owner.name(...)` calls: a member of the type `Owner` names, or a
    /// method of the extension block it names (LR12.2, LR42, LR76).
    fn qualified(&mut self, owner: &str, name: &str, span: Span) -> Option<Callee> {
        // A local of that name holds a value, and a value is not a type or a
        // block.
        if self.shadowed(owner) {
            return None;
        }

        if owner == "Result" && matches!(name, "Ok" | "Err") {
            let params = vec!["T".to_owned(), "E".to_owned()];
            let carried = usize::from(name == "Err");
            return Some(Callee {
                name: format!("Result.{name}"),
                overloads: vec![Signature {
                    asynchronous: false,
                    type_params: params.clone(),
                    constraints: Vec::new(),
                    params: vec![crate::table::Param {
                        name: "value".to_owned(),
                        ty: Type::Parameter(params[carried].clone()),
                        optional: false,
                        variadic: false,
                    }],
                    result: Type::Builtin {
                        kind: Builtin::Result,
                        args: params.into_iter().map(Type::Parameter).collect(),
                    },
                    takes_self: false,
                    visibility: None,
                    span,
                    inferred: false,
                    unsafe_: false,
                }],
                receiver: None,
            });
        }

        // LR15.3: `Enum.Variant(...)` builds a value of the enum, and its
        // payload is checked the way a call checks its arguments.
        if let Some((built, Variant::Tuple(payload))) = self.variant(owner, name) {
            return Some(Callee {
                name: format!("{owner}.{name}"),
                overloads: vec![Signature {
                    asynchronous: false,
                    type_params: Vec::new(),
                    constraints: Vec::new(),
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
                    inferred: false,
                    unsafe_: false,
                }],
                receiver: None,
            });
        }

        // A block is known by the name this module binds it to, and only where
        // it is in scope (LR20).
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

    /// LR11.1, LR11.5: an operand a built-in operator does not take, reported
    /// where it is written. `integers` is what tells bitwise from arithmetic.
    fn built_in_operand(
        &mut self,
        spelling: &str,
        integers: bool,
        held: &Type,
        span: Span,
    ) -> bool {
        let fits = if integers {
            is_integer(held)
        } else {
            is_numeric(held)
        };
        if fits || opaque(held) {
            return true;
        }

        let (code, wanted) = if integers {
            (codes::BITWISE_OPERANDS, "integers")
        } else {
            (codes::ARITHMETIC_OPERANDS, "numbers")
        };

        self.diagnostics.push(Diagnostic::error(
            code,
            span,
            format!("`{spelling}` takes {wanted}, and this is {}", article(held)),
        ));

        false
    }

    /// LR36: an operator on a type it is not built in for calls the protocol
    /// method it names, found the way any other method is (LR76). Dispatch is
    /// on the left operand, and neither side is converted first.
    fn overloaded(
        &mut self,
        spelling: &str,
        protocol: &str,
        method: &str,
        receiver: &Type,
        operand: Option<(&Type, Span)>,
        span: Span,
    ) -> Type {
        if opaque(receiver) {
            return Type::Unresolved;
        }

        let arity = usize::from(operand.is_some());
        let candidates: Vec<Signature> = self
            .find_method(receiver, method, span)
            .unwrap_or_default()
            .into_iter()
            .filter(|signature| signature.takes_self && signature.params.len() == arity)
            .collect();

        if candidates.is_empty() {
            // LR23.1: a decorator that has not run could still add it.
            if !self.expands(receiver) {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::OPERATOR_NOT_OVERLOADED,
                        span,
                        format!("`{spelling}` is not defined for {}", article(receiver)),
                    )
                    .note(format!(
                        "`{spelling}` calls `{method}`, which comes from `{protocol}` (LR36)."
                    )),
                );
            }
            return Type::Unresolved;
        }

        let Some((held, operand_span)) = operand else {
            return self.resolved(&candidates[0], span);
        };

        let fitting: Vec<&Signature> = candidates
            .iter()
            .filter(|signature| self.accepts(&signature.params[0].ty, held))
            .collect();

        match fitting.as_slice() {
            [only] => self.resolved(only, span),
            [] => {
                if !matches!(held, Type::Unresolved) {
                    let wanted = candidates[0].params[0].ty.clone();
                    self.expect_argument(&wanted, held, operand_span);
                }
                Type::Unresolved
            }
            _ => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::AMBIGUOUS_OVERLOAD,
                        span,
                        format!("{} fits more than one `{method}`", article(held)),
                    )
                    .note("Overloads are told apart by their parameters (LR40)."),
                );
                Type::Unresolved
            }
        }
    }

    /// What an operator produces, written down at the operator's own span so
    /// that lowering reaches the same method the checker did (LR36, LR55).
    fn resolved(&mut self, signature: &Signature, span: Span) -> Type {
        self.facts.record_call(span, signature.span);
        self.facts.record_type(span, signature.result.clone());
        signature.result.clone()
    }

    /// Whether a decorator that has not run could still add members (LR23.1).
    fn expands(&self, ty: &Type) -> bool {
        let Type::Named { module, name, .. } = ty else {
            return false;
        };

        match self.table.get(*module, name) {
            Some(Decl::Struct(structure)) => structure.expands,
            Some(Decl::Interface(interface)) => interface.expands,
            Some(Decl::Enum(enumeration)) => enumeration.expands,
            _ => false,
        }
    }

    /// LR39: arithmetic is on one numeric type, and there is no promotion
    /// between two. A literal takes the type of the other operand where it
    /// fits, which is what keeps `count + 1` writable.
    fn arithmetic(&mut self, op: BinaryOp, left: &Type, right: &Type, span: Span) -> Type {
        // Two literals are worked out here, so that what the expression is
        // worth is known where the bounds are checked (LR39).
        if let (Type::IntegerLiteral(left), Type::IntegerLiteral(right)) = (left, right) {
            return match fold(op, *left, *right) {
                Some(value) => Type::IntegerLiteral(value),
                None => Type::Primitive(Primitive::I64),
            };
        }

        if left == right {
            return left.clone();
        }

        // Only two numbers are this rule's business.
        if !is_numeric(left) || !is_numeric(right) {
            return Type::Unresolved;
        }

        // LR39: a literal is polymorphic until something asks for a type, and
        // the other operand is what asks.
        for (literal, concrete) in [(left, right), (right, left)] {
            if matches!(literal, Type::IntegerLiteral(_) | Type::FloatLiteral)
                && concrete.accepts(literal)
            {
                return concrete.clone();
            }
        }

        self.diagnostics.push(
            Diagnostic::error(
                codes::MIXED_ARITHMETIC,
                span,
                format!("this mixes {} and {}", article(left), article(right)),
            )
            .note("Write the conversion, as in `a as i64 + b` (LR39, LR33)."),
        );

        Type::Unresolved
    }

    /// LR33: `as` is the safe conversion between numeric types, and nothing
    /// wider. A conversion that can fail is an API returning an optional or a
    /// `Result`, and a representation cast is `unsafe` (LR29.2).
    fn convertible(&mut self, held: &Type, wanted: &Type, span: Span) {
        // A pointer cast is a representation cast, which has its own rule.
        let opaque = |ty: &Type| {
            matches!(
                ty,
                Type::Unresolved
                    | Type::Pointer { .. }
                    | Type::Parameter(_)
                    | Type::Primitive(Primitive::Any | Primitive::Unknown)
            )
        };
        if opaque(held) || opaque(wanted) {
            return;
        }

        // Converting a type to itself is a conversion that does nothing, and
        // saying so is how a reader spells out what a literal is.
        if held == wanted || (is_numeric(held) && is_numeric(wanted)) {
            return;
        }

        self.diagnostics.push(
            Diagnostic::error(
                codes::INVALID_CAST,
                span,
                format!("`as` does not convert {} to `{wanted}`", article(held)),
            )
            .note("`as` converts between numeric types (LR33, LR39)."),
        );
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
        let declared = self.unnarrowed(name);

        // What a condition proved wins over what the declaration said, for as
        // long as the branch that proved it lasts (LR57).
        for scope in self.narrowed.iter().rev() {
            if let Some(ty) = scope.get(name) {
                return ty.clone();
            }
        }

        declared
    }

    /// The type `name` was declared with, with nothing a condition proved
    /// laid over it.
    fn unnarrowed(&mut self, name: &str) -> Type {
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

    fn mark_capture_mutable(&mut self, name: &str) {
        let Some(index) = self
            .values
            .iter()
            .enumerate()
            .rev()
            .find_map(|(index, scope)| scope.contains_key(name).then_some(index))
        else {
            return;
        };

        for closure in &mut self.closures {
            if index < closure.base {
                closure.mutable.insert(name.to_owned());
            }
        }
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
            // LR36: a type these are not built in for reaches them through
            // the protocol each names.
            UnaryOp::Negate if !is_numeric(&held) => {
                self.overloaded("-", "Neg", "neg", &held, None, operand.span)
            }
            UnaryOp::BitNot if !is_numeric(&held) => {
                self.overloaded("~", "BitNot", "bitNot", &held, None, operand.span)
            }
            // LR11.5: a number that is not an integer has no bit pattern this
            // operator is defined over.
            UnaryOp::BitNot if !self.built_in_operand("~", true, &held, operand.span) => {
                Type::Unresolved
            }
            UnaryOp::Negate | UnaryOp::BitNot => held,
        }
    }

    fn binary(&mut self, op: BinaryOp, op_span: Span, left: &Expr, right: &Expr) -> Type {
        let held_left = self.expr(left);

        // LR11.4, LR57: the right side of `and` runs only where the left held,
        // so it is checked knowing what the left proved.
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
            BinaryOp::Divide if !is_numeric(&held_left) => self.overloaded(
                "/",
                "Div",
                "div",
                &held_left,
                Some((&held_right, right.span)),
                op_span,
            ),
            BinaryOp::Divide if !self.built_in_operand("/", false, &held_right, right.span) => {
                Type::Unresolved
            }
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
            // LR11.3: comparison is built in for the primitive types. Every
            // other type reaches it through `Eq` or `Comparable` (LR36), and
            // either way the answer is a `bool`.
            BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::Less
            | BinaryOp::LessEqual
            | BinaryOp::Greater
            | BinaryOp::GreaterEqual => {
                if !compared_builtin(&held_left, &held_right)
                    && let Some((spelling, protocol, method)) = protocol_of(op)
                {
                    let produced = self.overloaded(
                        spelling,
                        protocol,
                        method,
                        &held_left,
                        Some((&held_right, right.span)),
                        op_span,
                    );

                    // LR36: the operator answers `bool` whatever the method
                    // answers, so the protocol is what pins the method down.
                    let wanted = if protocol == "Eq" {
                        Type::BOOL
                    } else {
                        Type::Primitive(Primitive::I64)
                    };

                    if !matches!(produced, Type::Unresolved) && !wanted.accepts(&produced) {
                        self.diagnostics.push(
                            Diagnostic::error(
                                codes::PROTOCOL_RESULT,
                                op_span,
                                format!(
                                    "`{method}` returns {}, and `{protocol}` returns `{wanted}`",
                                    article(&produced)
                                ),
                            )
                            .note(format!(
                                "`{spelling}` answers a `bool` however `{method}` \
                                 answers, so the protocol fixes it (LR36)."
                            )),
                        );
                    }
                }

                Type::BOOL
            }
            // LR11.2: both operands are already `string`, which is what keeps
            // `..` unoverloadable (LR36).
            BinaryOp::Concat => {
                for (held, operand) in [(&held_left, left), (&held_right, right)] {
                    if !Type::STRING.accepts(held) {
                        self.diagnostics.push(
                            Diagnostic::error(
                                codes::CONCAT_OPERANDS,
                                operand.span,
                                format!("`..` joins two strings, and this is {}", article(held)),
                            )
                            .note(
                                "Nothing is stringified on its way in. Write an \
                                 interpolated string, or use `Display` (LR11.2, LR4.6).",
                            ),
                        );
                    }
                }

                Type::STRING
            }
            // LR8: `??` produces what the left side holds when it is present.
            BinaryOp::Coalesce => match held_left {
                Type::Optional(inner) => *inner,
                _ => Type::Unresolved,
            },
            // Arithmetic and bitwise on one numeric type produce it (LR39).
            // Every other type reaches them through the protocol the operator
            // names (LR36).
            _ => match protocol_of(op) {
                Some((spelling, protocol, method)) if !is_numeric(&held_left) => self.overloaded(
                    spelling,
                    protocol,
                    method,
                    &held_left,
                    Some((&held_right, right.span)),
                    op_span,
                ),
                _ => {
                    // LR11.1, LR11.5: both sides are numbers, and bitwise
                    // narrows that to integers.
                    let spelling = protocol_of(op).map_or("", |(spelling, _, _)| spelling);
                    let integers = bitwise(op);
                    let fits = [(&held_left, left.span), (&held_right, right.span)]
                        .into_iter()
                        .fold(true, |fits, (held, at)| {
                            self.built_in_operand(spelling, integers, held, at) && fits
                        });

                    if fits {
                        self.arithmetic(op, &held_left, &held_right, op_span)
                    } else {
                        Type::Unresolved
                    }
                }
            },
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

    fn destructured_field(&self, held: &Type, name: &str) -> Option<DestructuredField> {
        match held {
            Type::Record(fields) => fields
                .iter()
                .find(|(field, _)| field == name)
                .map(|(_, ty)| (ty.clone(), None)),
            Type::Named {
                module,
                name: declared,
                args,
            } => {
                let Some(Decl::Struct(structure)) = self.table.get(*module, declared) else {
                    return None;
                };
                let field = structure.fields.iter().find(|field| field.name == name)?;
                Some((
                    substitute(&field.ty, &structure.type_params, args),
                    Some((field.visibility, *module, declared.clone())),
                ))
            }
            Type::Unresolved => Some((Type::Unresolved, None)),
            _ => None,
        }
    }

    fn bind_unresolved(&mut self, binding: &Binding) {
        for name in bound(binding) {
            self.bind(&name, Type::Unresolved);
        }
    }

    fn invalid_destructure(&mut self, span: Span, held: &Type) {
        self.diagnostics.push(
            Diagnostic::error(
                codes::INVALID_DESTRUCTURE,
                span,
                format!("cannot destructure {held}"),
            )
            .note(
                "Records, structs, and tuples destructure by their statically known shape (LR5.3).",
            ),
        );
    }

    fn closure_binding(&self, mut declared: Type, value: Option<&Type>) -> Type {
        let Type::Function { sendable, .. } = &mut declared else {
            return declared;
        };

        if let Some(Type::Function {
            sendable: value, ..
        }) = value
        {
            *sendable = *value;
        }

        declared
    }

    fn update_closure_binding(&mut self, name: &str, value: &Type) {
        let Type::Function {
            sendable: value, ..
        } = value
        else {
            return;
        };

        for scope in self.values.iter_mut().rev() {
            let Some(Type::Function { sendable, .. }) = scope.get_mut(name) else {
                continue;
            };
            *sendable &= *value;
            return;
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
    }

    fn pop(&mut self) {
        self.values.pop();
        self.constants.pop();
    }

    /// LR72: an address is taken inside `unsafe`, and only of a binding that
    /// stays put for the length of that context.
    fn address_of(&mut self, mutable: bool, operand: &Expr, span: Span) {
        let taking = if mutable { "`&mut`" } else { "`&`" };

        if self.unsafely == 0 {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::UNSAFE_REQUIRED,
                    span,
                    format!("{taking} takes a raw pointer, which needs `unsafe`"),
                )
                .note("Write it inside an `unsafe` block, or in an `unsafe` function (LR29.2)."),
            );
        }

        if !addressable(operand) {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::ADDRESS_OF_TEMPORARY,
                    operand.span,
                    "this is a value in flight, and has no address to take",
                )
                .note("An address is taken of a binding, a field of one, or an element (LR72)."),
            );
            return;
        }

        if let ExprKind::Name(name) = &operand.kind {
            self.facts.record_addressed(name.clone());
        }

        if let (true, ExprKind::Name(name)) = (mutable, &operand.kind)
            && self.is_constant(name)
        {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::ADDRESS_OF_CONSTANT,
                    operand.span,
                    format!("`{name}` is bound by `const`, and `&mut` writes through"),
                )
                .note("Take `&` of a `const` binding, or bind it with `local` (LR72, LR5.2)."),
            );
        }
    }

    /// LR24: a `const` is worked out while compiling, over a pure subset:
    /// literals, arithmetic and comparison, string operations, tuple, record
    /// and array construction, enum construction, and other `const` values.
    fn evaluable(&mut self, value: &Expr) {
        let reason = match &value.kind {
            ExprKind::Nil
            | ExprKind::Bool(_)
            | ExprKind::Integer(_)
            | ExprKind::Float(_)
            | ExprKind::String(_)
            | ExprKind::ByteString(_)
            | ExprKind::Char(_)
            | ExprKind::Error => return,

            // A name is const only where it reads another `const` (LR79).
            ExprKind::Name(name) => {
                if self.is_constant(name) {
                    return;
                }
                "reads a binding that is not `const`"
            }

            ExprKind::Unary { operand, .. } => return self.evaluable(operand),
            ExprKind::Cast { value, .. } => return self.evaluable(value),
            ExprKind::Binary { left, right, .. } => {
                self.evaluable(left);
                return self.evaluable(right);
            }
            ExprKind::Interpolation(parts) => {
                for part in parts {
                    if let InterpolationPart::Expr(expr) = part {
                        self.evaluable(expr);
                    }
                }
                return;
            }
            ExprKind::Tuple(items) | ExprKind::List(items) | ExprKind::Set(items) => {
                for item in items {
                    self.evaluable(item);
                }
                return;
            }
            ExprKind::Record { fields, .. } => {
                for field in fields {
                    self.evaluable(&field.value);
                }
                return;
            }
            ExprKind::Map(entries) => {
                for entry in entries {
                    if let MapKey::Computed(key) = &entry.key {
                        self.evaluable(key);
                    }
                    self.evaluable(&entry.value);
                }
                return;
            }

            // LR15.3: building an enum variant is construction, not a call.
            ExprKind::Call {
                callee,
                method,
                args,
                ..
            } => {
                if method.is_none()
                    && let ExprKind::Field { receiver, name, .. } = &callee.kind
                    && let ExprKind::Name(owner) = &receiver.kind
                    && self.variant(owner, name).is_some()
                {
                    for argument in args {
                        self.evaluable(&argument.value);
                    }
                    return;
                }

                "calls a function, which is not run while compiling"
            }
            ExprKind::Field { receiver, name, .. } => {
                if let ExprKind::Name(owner) = &receiver.kind
                    && self.variant(owner, name).is_some()
                {
                    return;
                }
                "reads a member, which needs the value it is read from"
            }

            ExprKind::Index { .. } => "reads an element, which needs the value it is read from",
            ExprKind::Function { .. } => "is a function, which has no value until it runs",
            ExprKind::Try(_) => "propagates an error, which needs something to have run",
            ExprKind::Await(_) => "suspends, which is not something compiling does",
            _ => "is not one of the forms a `const` is worked out from",
        };

        self.diagnostics.push(
            Diagnostic::error(
                codes::CONST_NOT_EVALUABLE,
                value.span,
                format!("this {reason}"),
            )
            .note(
                "A `const` is worked out from literals, operators, and other \
                 `const` values (LR24).",
            ),
        );
    }

    /// Marks the names a `const` bound, so that assigning to one is reported
    /// (LR5.2).
    fn bind_constant(&mut self, binding: &Binding) {
        for name in bound(binding) {
            self.constants
                .last_mut()
                .expect("a scope is open")
                .insert(name);
        }
    }

    /// Whether `name` reads a `const`, decided in the scope that binds the
    /// name rather than an outer one it shadows (LR53).
    fn is_constant(&self, name: &str) -> bool {
        for (values, constants) in self.values.iter().zip(&self.constants).rev() {
            if values.contains_key(name) {
                return constants.contains(name);
            }
        }

        // A module-level `const` is a name of the module, and stays one
        // through an import (LR21.3, LR24).
        let origin = self.names.scope(self.scope).get(name).map(|b| &b.origin);
        match origin {
            Some(Origin::Binding { constant, .. }) => *constant,
            Some(Origin::Imported { module, name }) => matches!(
                self.names.scope(*module).get(name).map(|b| &b.origin),
                Some(Origin::Binding { constant: true, .. })
            ),
            _ => false,
        }
    }

    /// What `condition` proves about the names it tests (LR57).
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
            // Both sides hold where `and` does, and the left is what makes the
            // right safe to write (LR11.4).
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

/// The unchecked collection and raw-pointer operations (LR29.2, LR70, LR72).
fn unsafe_memory_method(receiver: &Type, name: &str, span: Span) -> Option<Signature> {
    let int = Type::Primitive(Primitive::I64);
    let isize = Type::Primitive(Primitive::Isize);
    let unit = Type::Tuple(Vec::new());

    let (params, result) = match (receiver, name) {
        (Type::Array(element), "unchecked") => {
            (vec![memory_param("index", int)], element.as_ref().clone())
        }
        (
            Type::Builtin {
                kind: Builtin::List | Builtin::FrozenList,
                args,
            },
            "unchecked",
        ) => (
            vec![memory_param("index", int)],
            args.first().cloned().unwrap_or(Type::Unresolved),
        ),
        (Type::Array(element), "uncheckedSet") => (
            vec![
                memory_param("index", int),
                memory_param("value", element.as_ref().clone()),
            ],
            unit,
        ),
        (
            Type::Builtin {
                kind: Builtin::List,
                args,
            },
            "uncheckedSet",
        ) => (
            vec![
                memory_param("index", int),
                memory_param("value", args.first().cloned().unwrap_or(Type::Unresolved)),
            ],
            unit,
        ),
        (Type::Primitive(Primitive::Bytes), "unchecked") => (
            vec![memory_param("index", int)],
            Type::Primitive(Primitive::U8),
        ),
        (Type::Primitive(Primitive::Bytes), "uncheckedSet") => (
            vec![
                memory_param("index", int),
                memory_param("value", Type::Primitive(Primitive::U8)),
            ],
            unit,
        ),
        (Type::Pointer { target, .. }, "read") => (Vec::new(), target.as_ref().clone()),
        (
            Type::Pointer {
                mutable: true,
                target,
            },
            "write",
        ) => (vec![memory_param("value", target.as_ref().clone())], unit),
        (Type::Pointer { .. }, "add") => (vec![memory_param("offset", isize)], receiver.clone()),
        _ => return None,
    };

    Some(Signature {
        asynchronous: false,
        type_params: Vec::new(),
        constraints: Vec::new(),
        params,
        result,
        takes_self: true,
        visibility: None,
        span,
        inferred: false,
        unsafe_: true,
    })
}

fn frozen_method(receiver: &Type, name: &str, span: Span) -> Option<Signature> {
    if name != "frozen" {
        return None;
    }
    let Type::Builtin { kind, args } = receiver else {
        return None;
    };
    let kind = match kind {
        Builtin::List => Builtin::FrozenList,
        Builtin::Map => Builtin::FrozenMap,
        Builtin::Set => Builtin::FrozenSet,
        _ => return None,
    };
    Some(Signature {
        asynchronous: false,
        type_params: Vec::new(),
        constraints: Vec::new(),
        params: Vec::new(),
        result: Type::Builtin {
            kind,
            args: args.clone(),
        },
        takes_self: true,
        visibility: None,
        span,
        inferred: false,
        unsafe_: false,
    })
}

fn checked_index_method(receiver: &Type, name: &str, span: Span) -> Option<Signature> {
    if name != "get" {
        return None;
    }
    let Type::Builtin { kind, args } = receiver else {
        return None;
    };
    let (name, param, result) = match kind {
        Builtin::List | Builtin::FrozenList => (
            "index",
            Type::Primitive(Primitive::I64),
            args.first().cloned().unwrap_or(Type::Unresolved),
        ),
        Builtin::Map | Builtin::FrozenMap => (
            "key",
            args.first().cloned().unwrap_or(Type::Unresolved),
            args.get(1).cloned().unwrap_or(Type::Unresolved),
        ),
        _ => return None,
    };
    Some(Signature {
        asynchronous: false,
        type_params: Vec::new(),
        constraints: Vec::new(),
        params: vec![crate::table::Param {
            name: name.to_owned(),
            ty: param,
            optional: false,
            variadic: false,
        }],
        result: result.optional(),
        takes_self: true,
        visibility: None,
        span,
        inferred: false,
        unsafe_: false,
    })
}

/// LR13.3: `ids:contains(value)` on a set or a frozen set.
fn set_contains_method(receiver: &Type, name: &str, span: Span) -> Option<Signature> {
    if name != "contains" {
        return None;
    }
    let Type::Builtin {
        kind: Builtin::Set | Builtin::FrozenSet,
        args,
    } = receiver
    else {
        return None;
    };
    Some(Signature {
        asynchronous: false,
        type_params: Vec::new(),
        constraints: Vec::new(),
        params: vec![crate::table::Param {
            name: "value".to_owned(),
            ty: args.first().cloned().unwrap_or(Type::Unresolved),
            optional: false,
            variadic: false,
        }],
        result: Type::BOOL,
        takes_self: true,
        visibility: None,
        span,
        inferred: false,
        unsafe_: false,
    })
}

fn collection_mutation_method(
    receiver: &Type,
    name: &str,
    span: Span,
) -> Option<(CollectionMutation, Signature)> {
    let Type::Builtin { kind, args } = receiver else {
        return None;
    };
    let element = args.first().cloned().unwrap_or(Type::Unresolved);
    let mutation = match (kind, name) {
        (Builtin::List, "push") => CollectionMutation::ListPush,
        (Builtin::List, "pop") => CollectionMutation::ListPop,
        (Builtin::Set, "insert") => CollectionMutation::SetInsert,
        _ => return None,
    };
    let (params, result) = match mutation {
        CollectionMutation::ListPush | CollectionMutation::SetInsert => (
            vec![crate::table::Param {
                name: "value".to_owned(),
                ty: element,
                optional: false,
                variadic: false,
            }],
            Type::Tuple(Vec::new()),
        ),
        CollectionMutation::ListPop => (Vec::new(), element.optional()),
    };
    Some((
        mutation,
        Signature {
            asynchronous: false,
            type_params: Vec::new(),
            constraints: Vec::new(),
            params,
            result,
            takes_self: true,
            visibility: None,
            span,
            inferred: false,
            unsafe_: false,
        },
    ))
}

/// LR4.3: `x:wrappingAdd(y)` and its kin, on any integer type.
fn overflow_method(receiver: &Type, name: &str, span: Span) -> Option<(OverflowMethod, Signature)> {
    let held = settle(receiver.clone());
    if !is_integer(&held) {
        return None;
    }
    let (mode, op) = match name {
        "wrappingAdd" => (Overflow::Wrap, BinaryOp::Add),
        "wrappingSub" => (Overflow::Wrap, BinaryOp::Subtract),
        "wrappingMul" => (Overflow::Wrap, BinaryOp::Multiply),
        "saturatingAdd" => (Overflow::Saturate, BinaryOp::Add),
        "saturatingSub" => (Overflow::Saturate, BinaryOp::Subtract),
        "saturatingMul" => (Overflow::Saturate, BinaryOp::Multiply),
        "checkedAdd" => (Overflow::Check, BinaryOp::Add),
        "checkedSub" => (Overflow::Check, BinaryOp::Subtract),
        "checkedMul" => (Overflow::Check, BinaryOp::Multiply),
        _ => return None,
    };
    let result = match mode {
        Overflow::Check => held.clone().optional(),
        Overflow::Wrap | Overflow::Saturate => held.clone(),
    };
    Some((
        OverflowMethod { mode, op },
        Signature {
            asynchronous: false,
            type_params: Vec::new(),
            constraints: Vec::new(),
            params: vec![crate::table::Param {
                name: "other".to_owned(),
                ty: held,
                optional: false,
                variadic: false,
            }],
            result,
            takes_self: true,
            visibility: None,
            span,
            inferred: false,
            unsafe_: false,
        },
    ))
}

fn is_collection(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Builtin {
            kind: Builtin::List
                | Builtin::FrozenList
                | Builtin::Map
                | Builtin::FrozenMap
                | Builtin::Set
                | Builtin::FrozenSet,
            ..
        }
    )
}

fn is_frozen_collection(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Builtin {
            kind: Builtin::FrozenList | Builtin::FrozenMap | Builtin::FrozenSet,
            ..
        }
    )
}

fn memory_param(name: &str, ty: Type) -> crate::table::Param {
    crate::table::Param {
        name: name.to_owned(),
        ty,
        optional: false,
        variadic: false,
    }
}

fn intrinsic_signature(intrinsic: Intrinsic, span: Span) -> Signature {
    let (type_params, params, result) = match intrinsic {
        Intrinsic::Assert => (
            Vec::new(),
            vec![
                intrinsic_param("condition", Type::BOOL, false),
                intrinsic_param("message", Type::STRING, true),
            ],
            Type::Tuple(Vec::new()),
        ),
        Intrinsic::DebugAssert => (
            Vec::new(),
            vec![intrinsic_param("condition", Type::BOOL, false)],
            Type::Tuple(Vec::new()),
        ),
        Intrinsic::Panic => (
            Vec::new(),
            vec![intrinsic_param("message", Type::STRING, false)],
            Type::Primitive(Primitive::Never),
        ),
        Intrinsic::ListNew => collection_constructor(Builtin::List, &["T"]),
        Intrinsic::MapNew => collection_constructor(Builtin::Map, &["K", "V"]),
        Intrinsic::SetNew => collection_constructor(Builtin::Set, &["T"]),
    };
    Signature {
        asynchronous: false,
        type_params,
        constraints: Vec::new(),
        params,
        result,
        takes_self: false,
        visibility: None,
        span,
        inferred: false,
        unsafe_: false,
    }
}

fn collection_constructor(
    kind: Builtin,
    names: &[&str],
) -> (Vec<String>, Vec<crate::table::Param>, Type) {
    let type_params: Vec<String> = names.iter().map(|name| (*name).to_owned()).collect();
    let args = type_params.iter().cloned().map(Type::Parameter).collect();
    (type_params, Vec::new(), Type::Builtin { kind, args })
}

fn intrinsic_param(name: &str, ty: Type, optional: bool) -> crate::table::Param {
    crate::table::Param {
        name: name.to_owned(),
        ty,
        optional,
        variadic: false,
    }
}

fn unavailable_unsafe_memory_method(receiver: &Type, name: &str) -> bool {
    let memory_receiver = matches!(
        receiver,
        Type::Array(_)
            | Type::Pointer { .. }
            | Type::Primitive(Primitive::Bytes)
            | Type::Builtin {
                kind: Builtin::List | Builtin::FrozenList,
                ..
            }
    );
    memory_receiver
        && matches!(
            name,
            "unchecked" | "uncheckedSet" | "read" | "write" | "add"
        )
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
    match (left, right) {
        // LR39: the widest literal is the one that has to fit.
        (Type::IntegerLiteral(left), Type::IntegerLiteral(right)) => {
            Type::IntegerLiteral(left.max(right))
        }
        (left, right) if left == right => left,
        _ => Type::Unresolved,
    }
}

/// What two integer literals come to, where that is worth knowing (LR39).
fn fold(op: BinaryOp, left: u64, right: u64) -> Option<u64> {
    match op {
        BinaryOp::Add => left.checked_add(right),
        BinaryOp::Subtract => left.checked_sub(right),
        BinaryOp::Multiply => left.checked_mul(right),
        BinaryOp::Remainder => left.checked_rem(right),
        _ => None,
    }
}

/// Everything unwritten on either way through, which is what is still
/// unwritten where the two ways meet (LR5.1).
fn union(left: HashSet<String>, right: HashSet<String>) -> HashSet<String> {
    left.union(&right).cloned().collect()
}

fn assigned_items(items: &[Item]) -> HashSet<String> {
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

fn assigned_function(body: &FunctionBody) -> HashSet<String> {
    match body {
        FunctionBody::Block(block) => assigned(block),
        FunctionBody::Expr(_) => HashSet::new(),
    }
}

fn assigned(block: &Block) -> HashSet<String> {
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

/// Whether `expr` names storage that stays put, which is what an address can
/// be taken of (LR72).
fn addressable(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Name(_) => true,
        ExprKind::Field { receiver, .. } | ExprKind::Index { receiver, .. } => {
            addressable(receiver)
        }
        _ => false,
    }
}

/// Whether `as` counts this as a number to convert (LR39).
/// Whether comparison is built in for two operands (LR11.3). Everything else
/// compares through a protocol (LR36).
fn compared_builtin(left: &Type, right: &Type) -> bool {
    // LR8: `x == nil` asks whether an optional holds anything, whatever it
    // would hold.
    let nothing = Type::Primitive(Primitive::Nil);
    if *left == nothing || *right == nothing {
        return true;
    }

    matches!(
        left,
        Type::Primitive(_) | Type::IntegerLiteral(_) | Type::FloatLiteral | Type::Unresolved
    )
}

/// Whether nothing is known about what a type holds, so no member of it can
/// be reported missing.
fn opaque(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Unresolved | Type::Primitive(Primitive::Any | Primitive::Unknown)
    )
}

/// Whether an operator is bitwise, which narrows its operands from numbers to
/// integers (LR11.5).
fn bitwise(op: BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::BitAnd
            | BinaryOp::BitOr
            | BinaryOp::BitXor
            | BinaryOp::ShiftLeft
            | BinaryOp::ShiftRight
    )
}

/// The protocol an overloadable operator names, and the method it calls
/// (LR36). The operators the spec leaves built in have none.
pub fn protocol_of(op: BinaryOp) -> Option<(&'static str, &'static str, &'static str)> {
    let named = match op {
        BinaryOp::Equal => ("==", "Eq", "eq"),
        BinaryOp::NotEqual => ("~=", "Eq", "eq"),
        BinaryOp::Less => ("<", "Comparable", "compare"),
        BinaryOp::LessEqual => ("<=", "Comparable", "compare"),
        BinaryOp::Greater => (">", "Comparable", "compare"),
        BinaryOp::GreaterEqual => (">=", "Comparable", "compare"),
        BinaryOp::Add => ("+", "Add", "add"),
        BinaryOp::Subtract => ("-", "Sub", "sub"),
        BinaryOp::Multiply => ("*", "Mul", "mul"),
        BinaryOp::Divide => ("/", "Div", "div"),
        BinaryOp::Remainder => ("%", "Rem", "rem"),
        BinaryOp::Power => ("**", "Pow", "pow"),
        BinaryOp::BitAnd => ("&", "BitAnd", "bitAnd"),
        BinaryOp::BitOr => ("|", "BitOr", "bitOr"),
        BinaryOp::BitXor => ("^", "BitXor", "bitXor"),
        BinaryOp::ShiftLeft => ("<<", "Shl", "shl"),
        BinaryOp::ShiftRight => (">>", "Shr", "shr"),
        _ => return None,
    };

    Some(named)
}

fn is_numeric(ty: &Type) -> bool {
    match ty {
        Type::IntegerLiteral(_) | Type::FloatLiteral => true,
        Type::Primitive(primitive) => primitive.is_integer() || primitive.is_float(),
        _ => false,
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

fn result_variant(expr: &Expr) -> Option<&str> {
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
