//! What every declaration in the program is (LR12, LR15, LR17.1, LR18).
//!
//! Name resolution answers where a name comes from. This answers what it is:
//! the fields of a struct and their types, the variants of an enum, the
//! members of an interface, what an alias stands for, and the signature of
//! every function. It is what a field access, a call, and a conformance check
//! all read.
//!
//! Building it is two passes over the same declarations. The first records
//! only what kind each one is, which is readable straight from the syntax and
//! is what lets a type mention another type declared later, or in a module
//! read after this one. The second resolves the types they are written with.

use std::collections::BTreeMap;

use luar_ast::{Function, Item, Member, Semantics, Visibility};
use luar_diagnostics::{Diagnostic, codes};

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
    /// The parameters, without `self`.
    pub params: Vec<Param>,
    /// What it returns. A function that states nothing returns nothing.
    pub result: Type,
    /// Whether it takes `self`, which is what makes it a method (LR65).
    pub takes_self: bool,
    /// `private` narrows a method to its module (LR44). Only a member has
    /// one; a free function is reached through its module surface instead.
    pub visibility: Option<Visibility>,
}

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
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub semantics: Semantics,
    pub type_params: Vec<String>,
    pub fields: Vec<Field>,
    /// Computed members, which read like fields (LR43).
    pub properties: Vec<Field>,
    pub methods: BTreeMap<String, Signature>,
    /// The interfaces it claims to implement (LR18).
    pub implements: Vec<Type>,
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
    pub methods: BTreeMap<String, Signature>,
    pub properties: Vec<Field>,
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
    Function(Signature),
    /// The methods an extension adds, and what it adds them to (LR20).
    Extension {
        target: Type,
        methods: BTreeMap<String, Signature>,
    },
}

/// Every declaration of every module.
#[derive(Debug, Default)]
pub struct Table {
    kinds: Kinds,
    decls: BTreeMap<(ModuleId, String), Decl>,
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

    #[must_use]
    pub fn signature(&self, module: ModuleId, name: &str) -> Option<&Signature> {
        match self.get(module, name)? {
            Decl::Function(signature) => Some(signature),
            _ => None,
        }
    }

    #[must_use]
    pub fn kinds(&self) -> &Kinds {
        &self.kinds
    }
}

/// Reads every declaration in `graph`.
#[must_use]
pub fn build(graph: &Graph, names: &Names) -> (Table, Vec<Diagnostic>) {
    let kinds = collect_kinds(graph);
    let mut decls = BTreeMap::new();
    let mut diagnostics = Vec::new();

    for (module, node) in graph.modules() {
        let mut resolver = Resolver::new(names, &kinds, module);
        declare(
            &node.ast.items,
            module,
            &mut resolver,
            &mut decls,
            &mut diagnostics,
        );
    }

    // A method written outside its type's body is attached once every
    // declaration is read, because the type may be written after it (LR20).
    for (module, node) in graph.modules() {
        let mut resolver = Resolver::new(names, &kinds, module);
        attach(
            &node.ast.items,
            module,
            names,
            &mut resolver,
            &mut decls,
            &mut diagnostics,
        );
    }

    (Table { kinds, decls }, diagnostics)
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

fn declare(
    items: &[Item],
    module: ModuleId,
    resolver: &mut Resolver,
    decls: &mut BTreeMap<(ModuleId, String), Decl>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for item in items {
        let (name, decl) = match item {
            Item::Function(function) if function.name.len() == 1 => (
                function.name[0].clone(),
                Decl::Function(signature(function, None, resolver, diagnostics)),
            ),
            Item::Struct(structure) => {
                resolver.enter(&structure.type_params);

                let mut fields = Vec::new();
                let mut properties = Vec::new();
                let mut methods = BTreeMap::new();

                for member in &structure.members {
                    match member {
                        Member::Field(field) => fields.push(Field {
                            name: field.name.clone(),
                            ty: resolver.resolve(&field.ty, diagnostics),
                            visibility: field.visibility,
                        }),
                        Member::Property(property) => properties.push(Field {
                            name: property.name.clone(),
                            ty: resolver.resolve(&property.ty, diagnostics),
                            visibility: property.visibility,
                        }),
                        Member::Function {
                            visibility,
                            function,
                        } => {
                            if let Some(name) = function.name.last() {
                                methods.insert(
                                    name.clone(),
                                    signature(function, *visibility, resolver, diagnostics),
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
                    }),
                )
            }
            Item::Enum(enumeration) => {
                resolver.enter(&enumeration.type_params);

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
                                })
                                .collect(),
                        ),
                    };
                    variants.insert(variant.name.clone(), payload);
                }

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

                let mut methods = BTreeMap::new();
                let mut properties = Vec::new();

                for member in &interface.members {
                    match member {
                        luar_ast::InterfaceMember::Function(function) => {
                            if let Some(name) = function.name.last() {
                                methods.insert(
                                    name.clone(),
                                    signature(function, None, resolver, diagnostics),
                                );
                            }
                        }
                        luar_ast::InterfaceMember::Property { name, ty, .. } => {
                            properties.push(Field {
                                name: name.clone(),
                                ty: resolver.resolve(ty, diagnostics),
                                visibility: None,
                            });
                        }
                    }
                }

                resolver.leave();

                (
                    interface.name.clone(),
                    Decl::Interface(InterfaceType {
                        structural: interface.structural,
                        type_params: interface.type_params.clone(),
                        methods,
                        properties,
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
                let mut methods = BTreeMap::new();
                for function in &extend.functions {
                    if let Some(name) = function.name.last() {
                        methods.insert(
                            name.clone(),
                            signature(function, None, resolver, diagnostics),
                        );
                    }
                }

                (extend.name.clone(), Decl::Extension { target, methods })
            }
            Item::Conditional(conditional) => {
                for (_, items) in &conditional.branches {
                    declare(items, module, resolver, decls, diagnostics);
                }
                if let Some(items) = &conditional.otherwise {
                    declare(items, module, resolver, decls, diagnostics);
                }
                continue;
            }
            _ => continue,
        };

        decls.entry((module, name)).or_insert(decl);
    }
}

/// Attaches `function Type.method(...)` to the type it names (LR20).
///
/// A member the type already declares stays as declared. Two declarations of
/// one member is not a rule the spec states yet, and keeping the first is
/// what makes every later stage see one member rather than the last written.
fn attach(
    items: &[Item],
    module: ModuleId,
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
                    attach(items, module, names, resolver, decls, diagnostics);
                }
                if let Some(items) = &conditional.otherwise {
                    attach(items, module, names, resolver, decls, diagnostics);
                }
                continue;
            }
            _ => continue,
        };

        let (owner, name) = (&function.name[0], &function.name[1]);

        // LR20: the type's own module is where its methods are written.
        // Another module adds to it through an extension block, which the
        // reader can see imported.
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
        if let Some(Decl::Struct(structure)) = decls.get_mut(&(module, owner.clone())) {
            structure.methods.entry(name.clone()).or_insert(signature);
        }
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

    let result = match &function.result {
        Some(result) => resolver.resolve(result, diagnostics),
        None => Type::Tuple(Vec::new()),
    };

    resolver.leave();

    Signature {
        asynchronous: function.asynchronous,
        params,
        result,
        takes_self,
        visibility,
    }
}
