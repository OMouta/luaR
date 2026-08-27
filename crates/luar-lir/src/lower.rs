//! Turning a checked program into LIR.
//!
//! Two sweeps. The first gives every declared type and every function an id,
//! because a declaration may name one written later or in another module. The
//! second fills them in.
//!
//! Lowering never guesses. Where the checker left a type unsettled, or where
//! a construct has no lowering yet, the program keeps its shape and lowering
//! records a [`Gap`] naming what it did not do. A program with gaps is not one
//! the backend may be handed, so an unfinished compiler cannot quietly emit
//! code for a program it only half understood.

pub mod types;

mod names;

mod body;

use std::cell::Cell;
use std::collections::HashMap;

use luar_ast::{Function as AstFunction, Item, Member, Module, Semantics};
use luar_diagnostics::Span;
use luar_sema::facts::Facts;
use luar_sema::modules::{Graph, ModuleId};
use luar_sema::table::{Decl, EnumType, InterfaceType, Signature, StructType, Table, Variant};
use luar_sema::types::Type;

use crate::inst::{MethodId, Terminator, Trap};
use crate::lower::types::Ids;
use crate::program::{
    Enum, Field, FuncId, Function, Interface, Method, Nominal, Program, Shape, Struct,
};
use crate::ty::{Ty, TypeId};

/// Something the program does and lowering does not handle yet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Gap {
    pub span: Span,
    pub what: String,
}

/// A lowered program, and what lowering could not do to it.
#[derive(Debug)]
pub struct Lowered {
    pub program: Program,
    /// Empty for a program that lowered completely. Anything here means the
    /// LIR describes less than the source does.
    pub gaps: Vec<Gap>,
}

/// Lowers every module in `graph`, which the checker has already accepted.
#[must_use]
pub fn lower(graph: &Graph, table: &Table, facts: &Facts) -> Lowered {
    let mut lowering = Lowering {
        graph,
        table,
        facts,
        program: Program::default(),
        ids: Ids::new(),
        functions: HashMap::new(),
        virtuals: HashMap::new(),
        defaults: HashMap::new(),
        bodies: Vec::new(),
        gaps: Vec::new(),
    };

    lowering.name_types();
    lowering.build_types();
    lowering.declare_functions();
    lowering.lower_bodies();

    Lowered {
        program: lowering.program,
        gaps: lowering.gaps,
    }
}

struct Lowering<'a> {
    graph: &'a Graph,
    table: &'a Table,
    facts: &'a Facts,
    program: Program,
    ids: Ids,
    /// The function each declaration was given, by the span of the
    /// declaration. That span is what tells two overloads of one name apart
    /// (LR40) and what the checker recorded a call as reaching (LR76).
    functions: HashMap<Span, Callee>,
    /// The interface method each bodiless declaration stands for, by its
    /// span. A call reaching one dispatches at runtime (LR18.1).
    virtuals: HashMap<Span, MethodId>,
    /// The default written beside a field, by the type and the field it
    /// belongs to (LR12.2).
    defaults: HashMap<(TypeId, u32), luar_ast::Expr>,
    /// The bodies waiting to be lowered, once every function has an id for
    /// the calls between them to name.
    bodies: Vec<Pending>,
    gaps: Vec<Gap>,
}

/// What a call site needs to know about the function it reaches.
pub(super) struct Callee {
    pub id: FuncId,
    /// Whether the first argument is the receiver (LR65).
    pub takes_self: bool,
    /// The parameters, without `self`, in declaration order.
    pub params: Vec<Parameter>,
    /// Its type parameters, in declaration order. A call carries one argument
    /// for each, and passes its arguments at the parameter types with those
    /// put in place (LR19).
    pub type_params: Vec<String>,
}

pub(super) struct Parameter {
    pub name: String,
    pub ty: Ty,
    /// `...values`, which takes every argument from its position on (LR9.6).
    pub variadic: bool,
    /// Evaluated at the call site when the call leaves the argument out
    /// (LR9.4).
    pub default: Option<luar_ast::Expr>,
}

/// A declared function whose body has not been lowered yet.
struct Pending {
    id: FuncId,
    /// The names the entry block's parameters bind to, in order.
    names: Vec<String>,
    body: luar_ast::Block,
}

impl Lowering<'_> {
    fn gap(&mut self, span: Span, what: impl Into<String>) {
        self.gaps.push(Gap {
            span,
            what: what.into(),
        });
    }

    /// How a name written in `module` reads in the whole program.
    ///
    /// Two modules may declare one name, so a linkage name carries the module
    /// it came from. The graph keys modules by a resolved path, so no two
    /// share one.
    fn qualify(&self, module: ModuleId, name: &str) -> String {
        let path = self.graph.module(module).path.with_extension("");
        format!("{}.{name}", path.display()).replace('\\', "/")
    }

    /// Gives every declared type an id, so that one may name another.
    fn name_types(&mut self) {
        let named: Vec<(ModuleId, String)> = self
            .table
            .decls()
            .filter(|(_, _, decl)| {
                matches!(decl, Decl::Struct(_) | Decl::Enum(_) | Decl::Interface(_))
            })
            .map(|(module, name, _)| (module, name.to_owned()))
            .collect();

        for (module, name) in named {
            let id = TypeId(u32::try_from(self.ids.len()).expect("type count fits in u32"));
            self.ids.insert((module, name), id);
        }
    }

    /// Fills in what each declared type holds, in the order [`Self::name_types`]
    /// gave them ids.
    fn build_types(&mut self) {
        let mut ordered: Vec<((ModuleId, String), TypeId)> = self
            .ids
            .iter()
            .map(|(key, id)| (key.clone(), *id))
            .collect();
        ordered.sort_by_key(|(_, id)| *id);

        let table = self.table;
        for ((module, name), id) in ordered {
            let span = self.declaration_span(module, &name);
            let nominal = match table.get(module, &name) {
                Some(Decl::Struct(structure)) => self.structure(module, &name, structure, span, id),
                Some(Decl::Enum(enumeration)) => self.enumeration(module, &name, enumeration, span),
                Some(Decl::Interface(interface)) => {
                    self.interface(module, &name, interface, span, id)
                }
                _ => unreachable!("only declared types were named"),
            };

            let added = self.program.add_type(nominal);
            debug_assert_eq!(added, id, "types are built in the order they were named");
        }
    }

    fn structure(
        &mut self,
        module: ModuleId,
        name: &str,
        structure: &StructType,
        span: Span,
        id: TypeId,
    ) -> Nominal {
        let fields = self.fields(
            structure
                .fields
                .iter()
                .map(|field| (&field.name, &field.ty)),
            span,
        );

        // LR12.2: a field written with a default may be left out of a
        // literal, and the default is evaluated where the literal is written.
        for (index, default) in self.written_defaults(module, name).into_iter().enumerate() {
            if let Some(default) = default {
                let index = u32::try_from(index).expect("field count fits in u32");
                self.defaults.insert((id, index), default);
            }
        }

        Nominal {
            name: self.qualify(module, name),
            type_params: structure.type_params.clone(),
            shape: Shape::Struct(Struct {
                fields,
                reference: structure.semantics == Semantics::Ref,
            }),
            span,
        }
    }

    fn enumeration(
        &mut self,
        module: ModuleId,
        name: &str,
        enumeration: &EnumType,
        span: Span,
    ) -> Nominal {
        // LR15: a variant's tag is its position, and the position is the one
        // it was declared at rather than the order the table happens to hold.
        let declared = self.variant_order(module, name);

        let variants = declared
            .into_iter()
            .filter_map(|variant| {
                let payload = enumeration.variants.get(&variant)?;
                let fields = match payload {
                    Variant::Unit => Vec::new(),
                    Variant::Tuple(types) => {
                        let named: Vec<(String, &Type)> = types
                            .iter()
                            .enumerate()
                            .map(|(i, ty)| (i.to_string(), ty))
                            .collect();
                        self.fields(named.iter().map(|(name, ty)| (name, *ty)), span)
                    }
                    Variant::Record(fields) => {
                        self.fields(fields.iter().map(|field| (&field.name, &field.ty)), span)
                    }
                };
                Some(crate::program::Variant {
                    name: variant,
                    fields,
                })
            })
            .collect();

        Nominal {
            name: self.qualify(module, name),
            type_params: enumeration.type_params.clone(),
            shape: Shape::Enum(Enum { variants }),
            span,
        }
    }

    fn interface(
        &mut self,
        module: ModuleId,
        name: &str,
        interface: &InterfaceType,
        span: Span,
        id: TypeId,
    ) -> Nominal {
        // LR18.1: the slot a `CallVirtual` names is a method's position here,
        // so the order has to be one every module agrees on. The table holds
        // methods by name, which is that order.
        let mut methods = Vec::new();
        for (method, overloads) in &interface.methods {
            for signature in overloads {
                let params = signature
                    .params
                    .iter()
                    .map(|param| self.convert(&param.ty, span))
                    .collect();
                let result = self.convert(&signature.result, span);
                let slot = u32::try_from(methods.len()).expect("method count fits in u32");
                self.virtuals.insert(
                    signature.span,
                    MethodId {
                        interface: id,
                        slot,
                    },
                );
                methods.push(Method {
                    name: method.clone(),
                    params,
                    result,
                });
            }
        }

        Nominal {
            name: self.qualify(module, name),
            type_params: interface.type_params.clone(),
            shape: Shape::Interface(Interface {
                methods,
                implementors: Vec::new(),
            }),
            span,
        }
    }

    fn fields<'f>(
        &mut self,
        declared: impl Iterator<Item = (&'f String, &'f Type)>,
        span: Span,
    ) -> Vec<Field> {
        declared
            .map(|(name, ty)| Field {
                name: name.clone(),
                ty: self.convert(ty, span),
            })
            .collect()
    }

    /// The LIR type of `ty`, or [`Ty::Never`] with a gap recorded where it has
    /// no representation. Nothing reads a `never`, so the shape survives while
    /// the gap says the program did not lower.
    fn convert(&mut self, ty: &Type, span: Span) -> Ty {
        match types::convert(ty, &self.ids) {
            Ok(converted) => converted,
            Err(refused) => {
                self.gap(span, refused);
                Ty::Never
            }
        }
    }

    /// Gives every function with a body an id and a signature.
    fn declare_functions(&mut self) {
        let declarations = self.declarations();
        for (module, path, function) in declarations {
            self.declare(module, &path, &function);
        }
    }

    fn declare(&mut self, module: ModuleId, path: &str, function: &AstFunction) {
        let span = function.span;
        let Some(signature) = self.signature(span) else {
            // A signature the table never built means the declaration was
            // reported already.
            return;
        };

        let mut type_params = signature.type_params.clone();
        let mut params = Vec::new();
        let mut names = Vec::new();

        // LR65: a method takes its receiver as the first argument, which is
        // what `self` is once the call is written out in full.
        if signature.takes_self {
            match self.self_type(module, path) {
                Some((receiver, owner_params)) => {
                    names.push("self".to_owned());
                    for param in owner_params.iter().rev() {
                        if !type_params.contains(param) {
                            type_params.insert(0, param.clone());
                        }
                    }
                    params.push(receiver);
                }
                None => self.gap(span, "a method whose receiver has no type"),
            }
        }

        let mut taken = Vec::new();
        for (index, param) in signature.params.iter().enumerate() {
            let ty = self.convert(&param.ty, span);
            params.push(ty.clone());
            names.push(param.name.clone());
            taken.push(Parameter {
                name: param.name.clone(),
                ty,
                variadic: param.variadic,
                default: function
                    .params
                    .get(index)
                    .and_then(|written| written.default.clone()),
            });
        }
        let result = self.convert(&signature.result, span);

        let mut lowered = Function::new(self.qualify(module, path), params, result, span);
        lowered.type_params = type_params;
        lowered.asynchronous = signature.asynchronous;
        // Until the body is lowered the function says it never returns,
        // rather than returning something made up.
        lowered.block_mut(lowered.entry).term = Some(Terminator::Trap(Trap::Unreachable));

        let declared = lowered.type_params.clone();
        let id = self.program.add_function(lowered);
        self.functions.insert(
            span,
            Callee {
                id,
                takes_self: signature.takes_self,
                params: taken,
                type_params: declared,
            },
        );

        if function.exported && path == "main" {
            self.program.entry = Some(id);
        }

        self.bodies.push(Pending {
            id,
            names,
            body: function.body.clone().expect("declarations carry bodies"),
        });
    }

    /// Fills in every declared function's body.
    ///
    /// Every function has an id by now, so a call reaching one written later
    /// names it like any other.
    fn lower_bodies(&mut self) {
        let pending = std::mem::take(&mut self.bodies);
        let mut built = Vec::with_capacity(pending.len());
        let mut made = Vec::new();

        // A closure is a function nothing declared, so it takes an id after
        // every declaration has one (LR9.8). One counter across every body
        // keeps them apart, and taking them in order is what lets them be
        // added in order afterwards.
        let next = Cell::new(
            u32::try_from(self.program.functions().count()).expect("function count fits in u32"),
        );

        for pending in &pending {
            let context = body::Context {
                next_function: &next,
                facts: self.facts,
                ids: &self.ids,
                callees: &self.functions,
                virtuals: &self.virtuals,
                defaults: &self.defaults,
                program: &self.program,
            };
            let shell = self.program.function(pending.id).clone();
            let (function, closures, gaps) =
                body::Body::new(context, shell).lower(&pending.names, &pending.body);
            built.push((pending.id, function, gaps));
            made.extend(closures);
        }

        for (id, function, gaps) in built {
            *self.program.function_mut(id) = function;
            self.gaps.extend(gaps);
        }
        for (id, function) in made {
            let added = self.program.add_function(function);
            debug_assert_eq!(added, id, "closures are added in the order they took ids");
        }
    }

    /// The signature the table built for the declaration at `span`.
    fn signature(&self, span: Span) -> Option<Signature> {
        self.table
            .decls()
            .flat_map(|(_, _, decl)| overloads(decl))
            .find(|signature| signature.span == span)
            .cloned()
    }

    /// The type `self` takes in a method written at `path`, and the type
    /// parameters that type brings with it (LR19, LR65).
    fn self_type(&self, module: ModuleId, path: &str) -> Option<(Ty, Vec<String>)> {
        let owner = path.rsplit_once('.')?.0;

        if let Some(id) = self.ids.get(&(module, owner.to_owned())).copied() {
            let params = self.program.nominal(id).type_params.clone();
            let args = params.iter().cloned().map(Ty::Parameter).collect();
            return Some((Ty::Named { id, args }, params));
        }

        // LR20: a method an extension block adds is a method of the type the
        // block extends. The block's own name is not a type.
        let table = self.table;
        let Some(Decl::Extension { target, .. }) = table.get(module, owner) else {
            return None;
        };
        let target = types::convert(target, &self.ids).ok()?;
        let params = match &target {
            Ty::Named { args, .. } => args
                .iter()
                .filter_map(|arg| match arg {
                    Ty::Parameter(name) => Some(name.clone()),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        Some((target, params))
    }

    /// Every function declaration in the program that has a body, with the
    /// path naming it inside its module.
    fn declarations(&self) -> Vec<(ModuleId, String, AstFunction)> {
        let mut found = Vec::new();
        for (module, node) in self.graph.modules() {
            collect(&node.ast.items, module, &mut found);
        }
        found
    }

    fn declaration_span(&self, module: ModuleId, name: &str) -> Span {
        let node = self.graph.module(module);
        declared_at(&node.ast, name).unwrap_or(node.ast.span)
    }

    /// The default written beside each stored field of a struct, in the order
    /// the fields are declared (LR12.2).
    fn written_defaults(&self, module: ModuleId, name: &str) -> Vec<Option<luar_ast::Expr>> {
        let node = self.graph.module(module);
        node.ast
            .items
            .iter()
            .find_map(|item| match item {
                Item::Struct(structure) if structure.name == name => Some(
                    structure
                        .members
                        .iter()
                        .filter_map(|member| match member {
                            Member::Field(field) => Some(field.default.clone()),
                            _ => None,
                        })
                        .collect(),
                ),
                _ => None,
            })
            .unwrap_or_default()
    }

    fn variant_order(&self, module: ModuleId, name: &str) -> Vec<String> {
        let node = self.graph.module(module);
        node.ast
            .items
            .iter()
            .find_map(|item| match item {
                Item::Enum(enumeration) if enumeration.name == name => Some(
                    enumeration
                        .variants
                        .iter()
                        .map(|variant| variant.name.clone())
                        .collect(),
                ),
                _ => None,
            })
            .unwrap_or_default()
    }
}

fn overloads(decl: &Decl) -> Vec<&Signature> {
    match decl {
        Decl::Function(overloads) => overloads.iter().collect(),
        Decl::Struct(structure) => structure.methods.values().flatten().collect(),
        Decl::Interface(interface) => interface.methods.values().flatten().collect(),
        Decl::Extension { methods, .. } => methods.values().flatten().collect(),
        Decl::Enum(_) | Decl::Alias { .. } => Vec::new(),
    }
}

fn collect(items: &[Item], module: ModuleId, found: &mut Vec<(ModuleId, String, AstFunction)>) {
    for item in items {
        match item {
            Item::Function(function) if function.body.is_some() => {
                found.push((module, function.name.join("."), function.clone()));
            }
            Item::Struct(structure) => {
                for member in &structure.members {
                    if let Member::Function { function, .. } = member
                        && function.body.is_some()
                        && let Some(name) = function.name.last()
                    {
                        found.push((
                            module,
                            format!("{}.{name}", structure.name),
                            function.clone(),
                        ));
                    }
                }
            }
            Item::Extend(extend) => {
                for function in &extend.functions {
                    if function.body.is_some()
                        && let Some(name) = function.name.last()
                    {
                        found.push((module, format!("{}.{name}", extend.name), function.clone()));
                    }
                }
            }
            _ => {}
        }
    }
}

/// Where `name` was declared in `module`, if it names a type.
fn declared_at(module: &Module, name: &str) -> Option<Span> {
    module.items.iter().find_map(|item| match item {
        Item::Struct(structure) if structure.name == name => Some(structure.span),
        Item::Enum(enumeration) if enumeration.name == name => Some(enumeration.span),
        Item::Interface(interface) if interface.name == name => Some(interface.span),
        _ => None,
    })
}
