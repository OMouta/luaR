//! What every declaration in the program is (LR12, LR15, LR17.1, LR18).

use std::collections::BTreeMap;

use luar_ast::{Decorator, Function, Item, Member, Semantics, Visibility};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::aliases::{self, Aliases, Written};
use crate::annotations::Resolver;
use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin};
use crate::types::Type;

/// What kind of thing a declaration is, before anything about it is resolved.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Struct,
    Enum,
    Interface,
    Alias,
    Function,
    /// An `extend Name for T` block, which is a name and not a type (LR20).
    Extension,
}

impl Kind {
    /// Whether a declaration of this kind may be written as a type.
    #[must_use]
    pub fn is_type(self) -> bool {
        matches!(
            self,
            Self::Struct | Self::Enum | Self::Interface | Self::Alias
        )
    }
}

/// The kind of every declaration in the program.
#[derive(Debug, Default)]
pub struct Kinds(BTreeMap<(ModuleId, String), Kind>);

impl Kinds {
    #[must_use]
    pub fn get(&self, module: ModuleId, name: &str) -> Option<Kind> {
        self.0.get(&(module, name.to_owned())).copied()
    }

    #[must_use]
    pub fn is_type(&self, module: ModuleId, name: &str) -> bool {
        self.get(module, name).is_some_and(Kind::is_type)
    }
}

/// What a callable takes and gives back (LR9.1, LR9.3).
#[derive(Debug, Clone)]
pub struct Signature {
    pub asynchronous: bool,
    /// Its own type parameters, which a call works out from what it passes
    /// (LR19).
    pub type_params: Vec<String>,
    /// What `where` requires of them, by parameter (LR19).
    pub constraints: Vec<(String, Type)>,
    /// The parameters, without `self`.
    pub params: Vec<Param>,
    /// What it returns. A function that states nothing returns nothing.
    pub result: Type,
    /// Whether it takes `self`, which is what makes it a method (LR65).
    pub takes_self: bool,
    /// `private` narrows a method to its module (LR44). Only a member has
    /// one; a free function is reached through its module surface instead.
    pub visibility: Option<Visibility>,
    /// The declaration this came from, which is what tells two overloads of
    /// one name apart (LR40).
    pub span: Span,
    /// Whether the result was left for the compiler to work out (LR7).
    pub inferred: bool,
    /// Whether calling it needs an `unsafe` context (LR29.2, LR46).
    pub unsafe_: bool,
}

/// Every signature one name has (LR40). One is the ordinary case.
pub type Overloads = Vec<Signature>;

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: Type,
    /// Whether the call site may leave it out (LR9.4).
    pub optional: bool,
    /// `...values`, which takes the rest (LR9.6).
    pub variadic: bool,
}

/// A stored field of a struct (LR12.2).
#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub ty: Type,
    /// `private` narrows a member to its module (LR44).
    pub visibility: Option<Visibility>,
    /// Whether a literal may leave it out, which a default makes true
    /// (LR12.2). Only a stored field has one.
    pub optional: bool,
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub semantics: Semantics,
    pub type_params: Vec<String>,
    pub fields: Vec<Field>,
    /// Computed members, which read like fields (LR43).
    pub properties: Vec<Field>,
    pub methods: BTreeMap<String, Overloads>,
    /// The interfaces it claims to implement (LR18).
    pub implements: Vec<Type>,
    /// Whether expansion could still add members to it (LR23.1). Expansion
    /// does not happen yet, so the members recorded here are all of them only
    /// when this is false.
    pub expands: bool,
}

impl StructType {
    /// Whether the type declares `name`, under any of the three member forms
    /// that share one namespace (LR12.2).
    #[must_use]
    pub fn has_member(&self, name: &str) -> bool {
        self.methods.contains_key(name)
            || self.fields.iter().any(|field| field.name == name)
            || self.properties.iter().any(|property| property.name == name)
    }
}

#[derive(Debug, Clone)]
pub struct EnumType {
    pub type_params: Vec<String>,
    pub variants: BTreeMap<String, Variant>,
}

/// What a variant carries (LR15.2).
#[derive(Debug, Clone)]
pub enum Variant {
    Unit,
    Tuple(Vec<Type>),
    Record(Vec<Field>),
}

#[derive(Debug, Clone)]
pub struct InterfaceType {
    pub structural: bool,
    pub type_params: Vec<String>,
    pub methods: BTreeMap<String, Overloads>,
    pub properties: Vec<Field>,
    /// Whether expansion could still add members. See [`StructType::expands`].
    pub expands: bool,
}

#[derive(Debug, Clone)]
pub enum Decl {
    Struct(StructType),
    Enum(EnumType),
    Interface(InterfaceType),
    /// What an alias stands for (LR17.1).
    Alias {
        type_params: Vec<String>,
        target: Type,
    },
    Function(Overloads),
    /// The methods an extension adds, and what it adds them to (LR20).
    Extension {
        target: Type,
        methods: BTreeMap<String, Overloads>,
    },
}

/// Every declaration of every module.
#[derive(Debug, Default)]
pub struct Table {
    kinds: Kinds,
    decls: BTreeMap<(ModuleId, String), Decl>,
    aliases: Aliases,
}

impl Table {
    #[must_use]
    pub fn get(&self, module: ModuleId, name: &str) -> Option<&Decl> {
        self.decls.get(&(module, name.to_owned()))
    }

    #[must_use]
    pub fn structure(&self, module: ModuleId, name: &str) -> Option<&StructType> {
        match self.get(module, name)? {
            Decl::Struct(structure) => Some(structure),
            _ => None,
        }
    }

    /// Every signature the free function `name` has (LR40).
    #[must_use]
    pub fn overloads(&self, module: ModuleId, name: &str) -> Option<&Overloads> {
        match self.get(module, name)? {
            Decl::Function(overloads) => Some(overloads),
            _ => None,
        }
    }

    #[must_use]
    pub fn kinds(&self) -> &Kinds {
        &self.kinds
    }

    /// What every alias in the program stands for (LR17.1).
    #[must_use]
    pub fn aliases(&self) -> &Aliases {
        &self.aliases
    }

    /// Where every function whose result is left to be worked out was
    /// written (LR7).
    #[must_use]
    pub fn inferred(&self) -> Vec<Span> {
        let mut spans: Vec<Span> = Vec::new();

        for decl in self.decls.values() {
            let sets: Vec<&Overloads> = match decl {
                Decl::Function(overloads) => vec![overloads],
                Decl::Struct(structure) => structure.methods.values().collect(),
                Decl::Interface(interface) => interface.methods.values().collect(),
                Decl::Extension { methods, .. } => methods.values().collect(),
                Decl::Enum(_) | Decl::Alias { .. } => Vec::new(),
            };

            for signature in sets.into_iter().flatten() {
                if signature.inferred && !spans.contains(&signature.span) {
                    spans.push(signature.span);
                }
            }
        }

        spans
    }

    /// Writes the result worked out for the declaration at `span`, and says
    /// whether that changed anything (LR7).
    pub fn infer_result(&mut self, span: Span, result: &Type) -> bool {
        let mut changed = false;

        for signature in signatures_mut(&mut self.decls) {
            if signature.span != span || !signature.inferred || signature.result == *result {
                continue;
            }

            signature.result = result.clone();
            changed = true;
        }

        changed
    }

    /// Every declaration in the program, with the module declaring it.
    pub fn decls(&self) -> impl Iterator<Item = (ModuleId, &str, &Decl)> {
        self.decls
            .iter()
            .map(|((module, name), decl)| (*module, name.as_str(), decl))
    }
}

/// Every signature the table holds, in no particular order.
fn signatures_mut(
    decls: &mut BTreeMap<(ModuleId, String), Decl>,
) -> impl Iterator<Item = &mut Signature> {
    decls.values_mut().flat_map(|decl| {
        let sets: Vec<&mut Overloads> = match decl {
            Decl::Function(overloads) => vec![overloads],
            Decl::Struct(structure) => structure.methods.values_mut().collect(),
            Decl::Interface(interface) => interface.methods.values_mut().collect(),
            Decl::Extension { methods, .. } => methods.values_mut().collect(),
            Decl::Enum(_) | Decl::Alias { .. } => Vec::new(),
        };

        sets.into_iter().flatten()
    })
}

/// Reads every declaration in `graph`.
#[must_use]
pub fn build(graph: &Graph, names: &Names) -> (Table, Vec<Diagnostic>) {
    let kinds = collect_kinds(graph);
    let empty = Aliases::default();
    let mut decls = BTreeMap::new();
    let mut diagnostics = Vec::new();

    for (module, node) in graph.modules() {
        let mut resolver = Resolver::new(names, &kinds, &empty, module);
        declare(
            &node.ast.items,
            module,
            false,
            &mut resolver,
            &mut decls,
            &mut diagnostics,
        );
    }

    // A method written outside its type's body is attached once every
    // declaration is read, because the type may be written after it (LR20).
    for (module, node) in graph.modules() {
        let mut resolver = Resolver::new(names, &kinds, &empty, module);
        attach(
            &node.ast.items,
            module,
            false,
            names,
            &mut resolver,
            &mut decls,
            &mut diagnostics,
        );
    }

    // LR17.1: an alias is not a type of its own, so it is taken back out
    // before anything reads what is here.
    let (aliases, reported) = aliases::resolve(&written(graph, &decls));
    diagnostics.extend(reported);

    for decl in decls.values_mut() {
        expand(decl, &aliases);
    }

    (
        Table {
            kinds,
            decls,
            aliases,
        },
        diagnostics,
    )
}

/// Every alias in the program, as written, with the target the first pass
/// resolved it to.
fn written(graph: &Graph, decls: &BTreeMap<(ModuleId, String), Decl>) -> Vec<Written> {
    fn walk(
        items: &[Item],
        module: ModuleId,
        decls: &BTreeMap<(ModuleId, String), Decl>,
        found: &mut Vec<Written>,
    ) {
        for item in items {
            match item {
                Item::TypeAlias(alias) => {
                    let Some(Decl::Alias {
                        type_params,
                        target,
                    }) = decls.get(&(module, alias.name.clone()))
                    else {
                        continue;
                    };

                    found.push(Written {
                        module,
                        name: alias.name.clone(),
                        params: type_params.clone(),
                        target: target.clone(),
                        span: alias.span,
                    });
                }
                Item::Conditional(conditional) => {
                    for (_, items) in &conditional.branches {
                        walk(items, module, decls, found);
                    }
                    if let Some(items) = &conditional.otherwise {
                        walk(items, module, decls, found);
                    }
                }
                _ => {}
            }
        }
    }

    let mut found = Vec::new();
    for (module, node) in graph.modules() {
        walk(&node.ast.items, module, decls, &mut found);
    }
    found
}

/// Puts every alias in one declaration back to what it stands for.
fn expand(decl: &mut Decl, aliases: &Aliases) {
    fn field(field: &mut Field, aliases: &Aliases) {
        field.ty = aliases.expand(&field.ty);
    }

    fn signature(signature: &mut Signature, aliases: &Aliases) {
        for param in &mut signature.params {
            param.ty = aliases.expand(&param.ty);
        }
        signature.result = aliases.expand(&signature.result);
    }

    fn overloads(overloads: &mut BTreeMap<String, Overloads>, aliases: &Aliases) {
        for set in overloads.values_mut() {
            for held in set {
                signature(held, aliases);
            }
        }
    }

    match decl {
        Decl::Struct(structure) => {
            for held in structure.fields.iter_mut().chain(&mut structure.properties) {
                field(held, aliases);
            }
            overloads(&mut structure.methods, aliases);
            for claim in &mut structure.implements {
                *claim = aliases.expand(claim);
            }
        }
        Decl::Enum(enumeration) => {
            for variant in enumeration.variants.values_mut() {
                match variant {
                    Variant::Unit => {}
                    Variant::Tuple(types) => {
                        for ty in types {
                            *ty = aliases.expand(ty);
                        }
                    }
                    Variant::Record(fields) => {
                        for held in fields {
                            field(held, aliases);
                        }
                    }
                }
            }
        }
        Decl::Interface(interface) => {
            overloads(&mut interface.methods, aliases);
            for held in &mut interface.properties {
                field(held, aliases);
            }
        }
        Decl::Alias { target, .. } => *target = aliases.expand(target),
        Decl::Function(set) => {
            for held in set {
                signature(held, aliases);
            }
        }
        Decl::Extension { target, methods } => {
            *target = aliases.expand(target);
            overloads(methods, aliases);
        }
    }
}

/// The kind of each declaration, read from the syntax alone.
fn collect_kinds(graph: &Graph) -> Kinds {
    let mut kinds = Kinds::default();
    for (module, node) in graph.modules() {
        kinds_of(&node.ast.items, module, &mut kinds);
    }
    kinds
}

fn kinds_of(items: &[Item], module: ModuleId, kinds: &mut Kinds) {
    for item in items {
        let (name, kind) = match item {
            Item::Function(function) if function.name.len() == 1 => {
                (&function.name[0], Kind::Function)
            }
            Item::Struct(structure) => (&structure.name, Kind::Struct),
            Item::Enum(enumeration) => (&enumeration.name, Kind::Enum),
            Item::Interface(interface) => (&interface.name, Kind::Interface),
            Item::TypeAlias(alias) => (&alias.name, Kind::Alias),
            Item::Extend(extend) => (&extend.name, Kind::Extension),
            Item::Conditional(conditional) => {
                for (_, items) in &conditional.branches {
                    kinds_of(items, module, kinds);
                }
                if let Some(items) = &conditional.otherwise {
                    kinds_of(items, module, kinds);
                }
                continue;
            }
            _ => continue,
        };

        kinds.0.entry((module, name.clone())).or_insert(kind);
    }
}

/// The name `Self` stands under while an interface is waiting to learn which
/// type implements it (LR65).
pub const SELF: &str = "Self";

/// The type `Self` names inside a declaration: the declaration itself, with
/// its own type parameters standing where its arguments go (LR65).
fn itself(module: ModuleId, name: &str, type_params: &[String]) -> Type {
    Type::Named {
        module,
        name: name.to_owned(),
        args: type_params.iter().cloned().map(Type::Parameter).collect(),
    }
}

fn declare(
    items: &[Item],
    module: ModuleId,
    branching: bool,
    resolver: &mut Resolver,
    decls: &mut BTreeMap<(ModuleId, String), Decl>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for item in items {
        // LR40: a name may have several signatures, so a function adds to the
        // set the name already has rather than replacing it.
        if let Item::Function(function) = item
            && function.name.len() == 1
        {
            let name = &function.name[0];
            let signature = signature(function, None, resolver, diagnostics);
            let entry = decls
                .entry((module, name.clone()))
                .or_insert_with(|| Decl::Function(Overloads::new()));

            if let Decl::Function(overloads) = entry {
                overload(overloads, name, signature, branching, diagnostics);
            }
            continue;
        }

        let (name, decl) = match item {
            Item::Struct(structure) => {
                resolver.enter(&structure.type_params);
                resolver.enter_enclosing(itself(module, &structure.name, &structure.type_params));

                let mut fields = Vec::new();
                let mut properties = Vec::new();
                let mut methods = BTreeMap::new();
                let mut seen: BTreeMap<&str, Span> = BTreeMap::new();

                for member in &structure.members {
                    let (name, span) = match member {
                        Member::Field(field) => (&field.name, field.span),
                        Member::Property(property) => (&property.name, property.span),
                        Member::Function { function, .. } => match function.name.last() {
                            Some(name) => (name, function.span),
                            None => continue,
                        },
                    };

                    // LR12.2: fields, properties, and methods share one
                    // namespace.
                    let held = match member {
                        Member::Function { .. } => seen.get(name.as_str()).copied(),
                        _ => seen.get(name.as_str()).copied().or_else(|| {
                            methods
                                .get(name.as_str())
                                .and_then(|overloads: &Overloads| overloads.first())
                                .map(|signature| signature.span)
                        }),
                    };

                    if let Some(first) = held {
                        diagnostics.push(duplicate(&structure.name, name, span, Some(first)));
                        continue;
                    }

                    if !matches!(member, Member::Function { .. }) {
                        seen.insert(name, span);
                    }

                    match member {
                        Member::Field(field) => fields.push(Field {
                            name: field.name.clone(),
                            ty: resolver.resolve(&field.ty, diagnostics),
                            visibility: field.visibility,
                            optional: field.default.is_some(),
                        }),
                        Member::Property(property) => properties.push(Field {
                            name: property.name.clone(),
                            ty: resolver.resolve(&property.ty, diagnostics),
                            visibility: property.visibility,
                            optional: false,
                        }),
                        Member::Function {
                            visibility,
                            function,
                        } => {
                            if let Some(name) = function.name.last() {
                                overload(
                                    methods.entry(name.clone()).or_default(),
                                    name,
                                    signature(function, *visibility, resolver, diagnostics),
                                    false,
                                    diagnostics,
                                );
                            }
                        }
                    }
                }

                let implements = structure
                    .implements
                    .iter()
                    .map(|ty| resolver.resolve(ty, diagnostics))
                    .collect();

                resolver.leave_enclosing();
                resolver.leave();

                (
                    structure.name.clone(),
                    Decl::Struct(StructType {
                        semantics: structure.semantics,
                        type_params: structure.type_params.clone(),
                        fields,
                        properties,
                        methods,
                        implements,
                        expands: expands(&structure.decorators),
                    }),
                )
            }
            Item::Enum(enumeration) => {
                resolver.enter(&enumeration.type_params);
                resolver.enter_enclosing(itself(
                    module,
                    &enumeration.name,
                    &enumeration.type_params,
                ));

                let mut variants = BTreeMap::new();
                for variant in &enumeration.variants {
                    let payload = match &variant.payload {
                        None => Variant::Unit,
                        Some(luar_ast::VariantPayload::Tuple(types)) => Variant::Tuple(
                            types
                                .iter()
                                .map(|ty| resolver.resolve(ty, diagnostics))
                                .collect(),
                        ),
                        Some(luar_ast::VariantPayload::Record(fields)) => Variant::Record(
                            fields
                                .iter()
                                .map(|field| Field {
                                    name: field.name.clone(),
                                    ty: resolver.resolve(&field.ty, diagnostics),
                                    visibility: None,
                                    optional: false,
                                })
                                .collect(),
                        ),
                    };
                    variants.insert(variant.name.clone(), payload);
                }

                resolver.leave_enclosing();
                resolver.leave();

                (
                    enumeration.name.clone(),
                    Decl::Enum(EnumType {
                        type_params: enumeration.type_params.clone(),
                        variants,
                    }),
                )
            }
            Item::Interface(interface) => {
                resolver.enter(&interface.type_params);
                // LR65: inside an interface `Self` is whichever type
                // implements it, and conformance checking is what fills it in.
                resolver.enter_enclosing(Type::Parameter(SELF.to_owned()));

                let mut methods = BTreeMap::new();
                let mut properties = Vec::new();

                for member in &interface.members {
                    match member {
                        luar_ast::InterfaceMember::Function(function) => {
                            if let Some(name) = function.name.last() {
                                overload(
                                    methods.entry(name.clone()).or_default(),
                                    name,
                                    signature(function, None, resolver, diagnostics),
                                    false,
                                    diagnostics,
                                );
                            }
                        }
                        luar_ast::InterfaceMember::Property { name, ty, span } => {
                            // LR18: a structural claim is about behavior, and
                            // layout is not checkable at an API boundary.
                            if interface.structural {
                                diagnostics.push(
                                    Diagnostic::error(
                                        codes::STRUCTURAL_PROPERTY,
                                        *span,
                                        format!(
                                            "`{}` is structural, and states `{name}` as stored",
                                            interface.name
                                        ),
                                    )
                                    .note("A structural interface requires methods only (LR18)."),
                                );
                            }

                            properties.push(Field {
                                name: name.clone(),
                                ty: resolver.resolve(ty, diagnostics),
                                visibility: None,
                                optional: false,
                            });
                        }
                    }
                }

                resolver.leave_enclosing();
                resolver.leave();

                (
                    interface.name.clone(),
                    Decl::Interface(InterfaceType {
                        structural: interface.structural,
                        type_params: interface.type_params.clone(),
                        methods,
                        properties,
                        expands: expands(&interface.decorators),
                    }),
                )
            }
            Item::TypeAlias(alias) => {
                resolver.enter(&alias.type_params);
                let target = resolver.resolve(&alias.target, diagnostics);
                resolver.leave();

                (
                    alias.name.clone(),
                    Decl::Alias {
                        type_params: alias.type_params.clone(),
                        target,
                    },
                )
            }
            Item::Extend(extend) => {
                let target = resolver.resolve(&extend.target, diagnostics);
                resolver.enter_enclosing(target.clone());

                let mut methods: BTreeMap<String, Overloads> = BTreeMap::new();
                for function in &extend.functions {
                    if let Some(name) = function.name.last() {
                        overload(
                            methods.entry(name.clone()).or_default(),
                            name,
                            signature(function, None, resolver, diagnostics),
                            false,
                            diagnostics,
                        );
                    }
                }

                resolver.leave_enclosing();

                (extend.name.clone(), Decl::Extension { target, methods })
            }
            Item::Conditional(conditional) => {
                for (_, items) in &conditional.branches {
                    declare(items, module, true, resolver, decls, diagnostics);
                }
                if let Some(items) = &conditional.otherwise {
                    declare(items, module, true, resolver, decls, diagnostics);
                }
                continue;
            }
            _ => continue,
        };

        decls.entry((module, name)).or_insert(decl);
    }
}

/// Adds `signature` to the set `name` already has, unless one already there
/// cannot be told apart from it (LR40).
/// `branching` says the declaration sits inside `#if` (LR48), where every
/// branch is read but one is selected. Two branches writing one declaration
/// are the same declaration twice over, not two overloads, so the first is
/// kept and nothing is reported.
fn overload(
    overloads: &mut Overloads,
    name: &str,
    signature: Signature,
    branching: bool,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if let Some(first) = overloads
        .iter()
        .find(|held| indistinguishable(held, &signature))
    {
        if branching {
            return;
        }

        diagnostics.push(
            Diagnostic::error(
                codes::INDISTINGUISHABLE_OVERLOADS,
                signature.span,
                format!("`{name}` already has an overload taking these parameters"),
            )
            .label(first.span, "the one it cannot be told apart from")
            .note("Overloads differ in their parameters, and a result tells two apart (LR40)."),
        );
        return;
    }

    overloads.push(signature);
}

/// LR40: two signatures are told apart by their parameters, and by nothing
/// else. A result is not a parameter.
fn indistinguishable(left: &Signature, right: &Signature) -> bool {
    left.params.len() == right.params.len()
        && left
            .params
            .iter()
            .zip(&right.params)
            .all(|(left, right)| left.ty == right.ty)
}

/// Whether any of these decorators could add a member to what it is written
/// on (LR23.1).
fn expands(decorators: &[Decorator]) -> bool {
    decorators.iter().any(|decorator| {
        !matches!(
            decorator.name.as_str(),
            "inline" | "noinline" | "deprecated" | "cold" | "repr" | "test" | "extern" | "reflect"
        )
    })
}

/// A member declared twice (LR12.2). The first one is the one that stands.
fn duplicate(owner: &str, name: &str, span: Span, first: Option<Span>) -> Diagnostic {
    let mut reported = Diagnostic::error(
        codes::DUPLICATE_MEMBER,
        span,
        format!("`{owner}` already has a member `{name}`"),
    );
    if let Some(first) = first {
        reported = reported.label(first, "first declared here");
    }

    reported.note("Fields, properties, and methods share one namespace (LR12.2).")
}

/// Attaches `function Type.method(...)` to the type it names (LR20).
fn attach(
    items: &[Item],
    module: ModuleId,
    branching: bool,
    names: &Names,
    resolver: &mut Resolver,
    decls: &mut BTreeMap<(ModuleId, String), Decl>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for item in items {
        let function = match item {
            Item::Function(function) if function.name.len() == 2 => function,
            Item::Conditional(conditional) => {
                for (_, items) in &conditional.branches {
                    attach(items, module, true, names, resolver, decls, diagnostics);
                }
                if let Some(items) = &conditional.otherwise {
                    attach(items, module, true, names, resolver, decls, diagnostics);
                }
                continue;
            }
            _ => continue,
        };

        let (owner, name) = (&function.name[0], &function.name[1]);

        // LR20: the type's own module is where its methods are written.
        if let Some(Origin::Imported { .. } | Origin::Namespace(_)) = names
            .scope(module)
            .get(owner)
            .map(|binding| &binding.origin)
        {
            diagnostics.push(
                Diagnostic::error(
                    codes::METHOD_OUTSIDE_ITS_MODULE,
                    function.span,
                    format!("`{owner}` is declared in another module"),
                )
                .note("A module adds to a type it did not declare with `extend` (LR20)."),
            );
            continue;
        }

        let signature = signature(function, None, resolver, diagnostics);
        let Some(Decl::Struct(structure)) = decls.get_mut(&(module, owner.clone())) else {
            continue;
        };

        // LR12.2: attaching a method the type already has declares one member
        // twice, however far apart the two are written.
        let stored = structure.fields.iter().any(|field| field.name == *name)
            || structure
                .properties
                .iter()
                .any(|property| property.name == *name);

        if stored {
            diagnostics.push(duplicate(owner, name, function.span, None));
            continue;
        }

        overload(
            structure.methods.entry(name.clone()).or_default(),
            name,
            signature,
            branching,
            diagnostics,
        );
    }
}

/// The signature of a function, without the body.
fn signature(
    function: &Function,
    visibility: Option<Visibility>,
    resolver: &mut Resolver,
    diagnostics: &mut Vec<Diagnostic>,
) -> Signature {
    resolver.enter(&function.type_params);

    let mut params = Vec::new();
    let mut takes_self = false;

    for param in &function.params {
        let name = match &param.binding {
            luar_ast::Binding::Name(name) => name.clone(),
            _ => String::new(),
        };

        // LR65: `self` is written like any other parameter, and having one is
        // what makes the function a method.
        if name == "self" && params.is_empty() {
            takes_self = true;
            continue;
        }

        params.push(Param {
            name,
            ty: match &param.ty {
                Some(ty) => resolver.resolve(ty, diagnostics),
                None => Type::Unresolved,
            },
            optional: param.default.is_some(),
            variadic: param.variadic,
        });
    }

    // LR7: a function that writes no result has one worked out from what it
    // returns, which is a pass of its own.
    let result = match &function.result {
        Some(result) => resolver.resolve(result, diagnostics),
        None => Type::Unresolved,
    };

    let constraints = function
        .constraints
        .iter()
        .map(|constraint| {
            (
                constraint.parameter.clone(),
                resolver.resolve(&constraint.bound, diagnostics),
            )
        })
        .collect();

    resolver.leave();

    Signature {
        asynchronous: function.asynchronous,
        type_params: function.type_params.clone(),
        constraints,
        params,
        result,
        takes_self,
        visibility,
        span: function.span,
        inferred: function.result.is_none(),
        unsafe_: function.unsafe_,
    }
}
