//! Turning a checked program into LIR.

pub mod types;

mod names;

mod body;
mod derived;
mod throws;

use std::cell::Cell;
use std::collections::{HashMap, HashSet};

use luar_ast::{Binding, Function as AstFunction, Item, Member, Module, Semantics};
use luar_diagnostics::Span;
use luar_sema::check::runtime_symbol;
use luar_sema::facts::Facts;
use luar_sema::modules::{Graph, ModuleId};
use luar_sema::table::{Decl, EnumType, InterfaceType, Signature, StructType, Table, Variant};
use luar_sema::types::Type;

use crate::inst::{Inst, InstKind, MethodId, Terminator, Trap};
use crate::lower::types::Ids;
use crate::program::{
    Enum, Field, FuncId, Function, Implementation, Interface, Method, Nominal, Program, Shape,
    Struct,
};
use crate::ty::{Builtin, Ty, TypeId};

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

/// Whether debug-only source operations are included (LR49).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompilationMode {
    Debug,
    Release,
}

/// Lowers every module in `graph`, which the checker has already accepted.
#[must_use]
pub fn lower(graph: &Graph, table: &Table, facts: &Facts) -> Lowered {
    lower_in_mode(graph, table, facts, CompilationMode::Debug)
}

#[must_use]
pub fn lower_in_mode(
    graph: &Graph,
    table: &Table,
    facts: &Facts,
    mode: CompilationMode,
) -> Lowered {
    let mut lowering = Lowering {
        graph,
        table,
        facts,
        mode,
        program: Program::default(),
        ids: Ids::new(),
        functions: HashMap::new(),
        virtuals: HashMap::new(),
        defaults: HashMap::new(),
        properties: HashMap::new(),
        bodies: Vec::new(),
        derived: Vec::new(),
        displays: HashMap::new(),
        throwing: HashSet::new(),
        constants: HashMap::new(),
        gaps: Vec::new(),
    };

    lowering.collect_constants();
    lowering.name_types();
    lowering.build_types();
    lowering.find_throwing();
    lowering.declare_functions();
    lowering.declare_initializers();
    lowering.declare_finalizers();
    lowering.declare_properties();
    lowering.declare_derived();
    lowering.find_displays();
    lowering.build_vtables();
    lowering.lower_bodies();
    lowering.write_derived();

    Lowered {
        program: lowering.program,
        gaps: lowering.gaps,
    }
}

struct Lowering<'a> {
    graph: &'a Graph,
    table: &'a Table,
    facts: &'a Facts,
    mode: CompilationMode,
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
    /// The computed members of each type, by the type and the name they are
    /// reached under (LR43).
    properties: HashMap<(TypeId, String), Property>,
    /// The bodies waiting to be lowered, once every function has an id for
    /// the calls between them to name.
    bodies: Vec<Pending>,
    /// The members `@derive` wrote, waiting for a body (LR75).
    derived: Vec<(FuncId, Span, Type, String)>,
    /// The `display` of each struct and enum that has one (LR35).
    displays: HashMap<TypeId, FuncId>,
    /// The declarations an exception can escape, by the span of each
    /// (LR25.3).
    throwing: HashSet<Span>,
    /// Each module-level `const`, by the module and the name, with the span
    /// of its declaration and its initializer (LR24).
    constants: HashMap<(ModuleId, String), (Span, luar_ast::Expr)>,
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
    /// Whether an exception can escape it, which is what makes the call give
    /// back what it threw as well as what it returned (LR25.3).
    pub throws: bool,
    /// Whether the call produces a `Task` rather than the result (LR27).
    pub asynchronous: bool,
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

/// A computed member, and the functions it reads and writes through (LR43).
pub(super) struct Property {
    pub ty: Ty,
    pub get: FuncId,
    /// Absent where the property is read-only. Setters are explicit (LR43).
    pub set: Option<FuncId>,
}

/// A declared function whose body has not been lowered yet.
struct Pending {
    id: FuncId,
    module: ModuleId,
    /// What the entry block's parameters bind to, in order.
    bindings: Vec<Binding>,
    /// Whether an exception can escape it (LR25.3).
    throws: bool,
    body: luar_ast::Block,
}

/// What a function an exception can escape gives back: what it returned, or
/// what it threw (LR25.3).
pub(super) fn thrown_or(result: Ty) -> Ty {
    Ty::Builtin {
        kind: crate::ty::Builtin::Result,
        args: vec![result, Ty::Dynamic],
    }
}

impl Lowering<'_> {
    fn gap(&mut self, span: Span, what: impl Into<String>) {
        self.gaps.push(Gap {
            span,
            what: what.into(),
        });
    }

    /// How a name written in `module` reads in the whole program.
    fn qualify(&self, module: ModuleId, name: &str) -> String {
        let path = self.graph.module(module).path.with_extension("");
        format!("{}.{name}", path.display()).replace('\\', "/")
    }

    fn collect_constants(&mut self) {
        for (module, node) in self.graph.modules() {
            for item in &node.ast.items {
                if let Item::Stmt(stmt) = item
                    && let luar_ast::StmtKind::Const {
                        binding: Binding::Name(name),
                        value,
                        ..
                    } = &stmt.kind
                {
                    self.constants
                        .insert((module, name.clone()), (stmt.span, value.clone()));
                }
            }
        }
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

        // LR12.2: a field written with a default may be left out of a literal,
        // and the default is evaluated where the literal is written.
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
                repr_c: self.repr_c(module, name),
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
        // so the order has to be one every module agrees on.
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
                    throws: false,
                    asynchronous: signature.asynchronous,
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
    /// Works out which declarations an exception can escape, before any of
    /// them takes a result type (LR25.3).
    fn find_throwing(&mut self) {
        let bodies: Vec<(Span, luar_ast::Block)> = self
            .declarations()
            .into_iter()
            .filter_map(|(_, _, function)| Some((function.span, function.body?)))
            .collect();
        let interfaces = self
            .table
            .decls()
            .filter(|(_, _, decl)| matches!(decl, Decl::Interface(_)))
            .map(|(module, name, _)| (module, name.to_owned()))
            .collect();
        self.throwing = throws::escaping(&bodies, self.facts, &interfaces);
    }

    fn declare_functions(&mut self) {
        let declarations = self.declarations();
        for (module, path, function) in declarations {
            self.declare(module, &path, &function);
        }
    }

    fn declare_initializers(&mut self) {
        for module in initialization_order(self.graph) {
            let node = self.graph.module(module);
            let stmts = node
                .ast
                .items
                .iter()
                .filter_map(|item| match item {
                    Item::Stmt(stmt) => Some(stmt.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            if stmts.is_empty() {
                continue;
            }

            let mut function = Function::new(
                self.qualify(module, "$init"),
                Vec::new(),
                Ty::Unit,
                node.ast.span,
            );
            function.block_mut(function.entry).term = Some(Terminator::Trap(Trap::Unreachable));
            let id = self.program.add_function(function);
            self.program.initializers.push(id);
            self.bodies.push(Pending {
                module,
                id,
                bindings: Vec::new(),
                throws: false,
                body: luar_ast::Block {
                    stmts,
                    span: node.ast.span,
                },
            });
        }
    }

    fn declare_finalizers(&mut self) {
        let mut found = Vec::new();
        for (module, node) in self.graph.modules() {
            for item in &node.ast.items {
                let Item::Struct(structure) = item else {
                    continue;
                };
                if structure.semantics != Semantics::Ref {
                    continue;
                }
                for member in &structure.members {
                    let Member::Function { function, .. } = member else {
                        continue;
                    };
                    if is_finalizer(function) {
                        found.push((module, structure.name.clone(), function.clone()));
                    }
                }
            }
        }

        for (module, owner, function) in found {
            let Some(id) = self.ids.get(&(module, owner.clone())).copied() else {
                continue;
            };
            let params = self.program.nominal(id).type_params.clone();
            let receiver = Ty::Named {
                id,
                args: params.iter().cloned().map(Ty::Parameter).collect(),
            };
            let name = function.name.last().cloned().unwrap_or_default();
            let mut lowered = Function::new(
                self.qualify(module, &format!("{owner}.{name}")),
                vec![receiver.clone()],
                Ty::Unit,
                function.span,
            );
            lowered.type_params = params;
            lowered.block_mut(lowered.entry).term = Some(Terminator::Trap(Trap::Unreachable));
            let finalizer = self.program.add_function(lowered);
            self.program.set_finalizer(receiver, finalizer);
            self.bodies.push(Pending {
                module,
                id: finalizer,
                bindings: vec![Binding::Name("self".to_owned())],
                throws: false,
                body: function.body.expect("a finalizer has a body"),
            });
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
        let mut bindings = Vec::new();

        // LR65: a method takes its receiver as the first argument, which is
        // what `self` is once the call is written out in full.
        if signature.takes_self {
            match self.self_type(module, path) {
                Some((receiver, owner_params)) => {
                    bindings.push(Binding::Name("self".to_owned()));
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
            let written = function
                .params
                .get(index + usize::from(signature.takes_self));
            let ty = self.convert(&param.ty, span);
            params.push(if param.variadic {
                Ty::Builtin {
                    kind: Builtin::FrozenList,
                    args: vec![ty.clone()],
                }
            } else {
                ty.clone()
            });
            bindings.push(
                written
                    .map(|param| param.binding.clone())
                    .unwrap_or_else(|| Binding::Name(param.name.clone())),
            );
            taken.push(Parameter {
                name: param.name.clone(),
                ty,
                variadic: param.variadic,
                default: written.and_then(|param| param.default.clone()),
            });
        }
        let declared = self.convert(&signature.result, span);
        // LR25.3: exceptions are absent from signatures, so a function an
        // exception can escape gives back either what it returned or what it
        // threw, and every call to it says which happened.
        let throws = self.throwing.contains(&span);
        let result = if throws {
            thrown_or(declared)
        } else {
            declared
        };

        let mut lowered = Function::new(self.qualify(module, path), params, result, span);
        lowered.type_params = type_params;
        lowered.asynchronous = signature.asynchronous;
        lowered.inline = inline(function);
        lowered.external = extern_symbol(function);
        lowered.c_abi = lowered.external.is_some() && !is_intrinsic(function);
        if function.body.is_some() {
            // Until the body is lowered the function says it never returns.
            lowered.block_mut(lowered.entry).term = Some(Terminator::Trap(Trap::Unreachable));
        }

        let declared_params = lowered.type_params.clone();
        let id = self.program.add_function(lowered);
        self.functions.insert(
            span,
            Callee {
                id,
                takes_self: signature.takes_self,
                params: taken,
                type_params: declared_params,
                throws,
                asynchronous: signature.asynchronous,
            },
        );

        if function.exported && path == "main" {
            self.program.entry = Some(id);
        }

        if let Some(body) = &function.body {
            self.bodies.push(Pending {
                module,
                id,
                bindings,
                throws,
                body: body.clone(),
            });
        }
    }

    /// Gives every computed member the functions it is read and written
    /// through (LR43).
    fn declare_properties(&mut self) {
        let mut found = Vec::new();
        for (module, node) in self.graph.modules() {
            for item in &node.ast.items {
                let Item::Struct(structure) = item else {
                    continue;
                };
                for member in &structure.members {
                    if let Member::Property(property) = member {
                        found.push((module, structure.name.clone(), property.clone()));
                    }
                }
            }
        }

        for (module, owner, property) in found {
            self.declare_property(module, &owner, &property);
        }
    }

    fn declare_property(&mut self, module: ModuleId, owner: &str, property: &luar_ast::Property) {
        let path = format!("{owner}.{}", property.name);
        let span = property.span;

        let (Some(id), Some((receiver, type_params))) = (
            self.ids.get(&(module, owner.to_owned())).copied(),
            self.self_type(module, &path),
        ) else {
            self.gap(span, "a property whose type the compiler could not find");
            return;
        };

        // The table resolved the declared type when it built the struct, so it
        // is read from there rather than resolved a second time.
        let declared = self
            .table
            .structure(module, owner)
            .and_then(|structure| {
                structure
                    .properties
                    .iter()
                    .find(|held| held.name == property.name)
            })
            .map(|held| held.ty.clone());
        let Some(declared) = declared else {
            self.gap(span, "a property the declaration table does not hold");
            return;
        };
        let ty = self.convert(&declared, span);

        let mut get = Function::new(
            self.qualify(module, &path),
            vec![receiver.clone()],
            ty.clone(),
            span,
        );
        get.type_params.clone_from(&type_params);
        get.block_mut(get.entry).term = Some(Terminator::Trap(Trap::Unreachable));
        let get = self.program.add_function(get);
        self.bodies.push(Pending {
            module,
            id: get,
            bindings: vec![Binding::Name("self".to_owned())],
            throws: false,
            body: property.get.clone(),
        });

        // LR43: a setter is written or the property is read-only.
        let set = property.set.as_ref().map(|setter| {
            let mut written = Function::new(
                self.qualify(module, &format!("{path}=")),
                vec![receiver, ty.clone()],
                Ty::Unit,
                setter.span,
            );
            written.type_params.clone_from(&type_params);
            written.block_mut(written.entry).term = Some(Terminator::Trap(Trap::Unreachable));
            let written = self.program.add_function(written);
            self.bodies.push(Pending {
                module,
                id: written,
                bindings: vec![
                    Binding::Name("self".to_owned()),
                    Binding::Name(setter.param.clone()),
                ],
                throws: false,
                body: setter.body.clone(),
            });
            written
        });

        self.properties
            .insert((id, property.name.clone()), Property { ty, get, set });
    }

    /// Records, for each interface, which types implement it and what each of
    /// its method slots resolves to for that type (LR18.1).
    fn build_vtables(&mut self) {
        let claims: Vec<(ModuleId, String, Vec<Type>)> = self
            .table
            .decls()
            .filter_map(|(module, name, decl)| match decl {
                Decl::Struct(structure) if !structure.implements.is_empty() => {
                    Some((module, name.to_owned(), structure.implements.clone()))
                }
                _ => None,
            })
            .collect();

        for (module, name, implements) in claims {
            let Some(ty) = self.ids.get(&(module, name.clone())).copied() else {
                continue;
            };
            for claimed in implements {
                self.implement(module, &name, ty, &claimed);
            }
        }
        self.adapt_throwing_virtuals();
    }

    /// Records that `ty` implements `claimed`, with the function each of the
    /// interface's methods resolves to.
    fn implement(&mut self, module: ModuleId, name: &str, ty: TypeId, claimed: &Type) {
        let span = self.declaration_span(module, name);
        let Ok(Ty::Named { id: interface, .. }) = self::types::convert(claimed, &self.ids) else {
            self.gap(span, "an interface the compiler could not find");
            return;
        };

        let Shape::Interface(held) = &self.program.nominal(interface).shape else {
            return;
        };
        let wanted: Vec<(String, usize)> = held
            .methods
            .iter()
            .map(|method| (method.name.clone(), method.params.len()))
            .collect();

        let Some(structure) = self.table.structure(module, name) else {
            return;
        };

        let mut methods = Vec::with_capacity(wanted.len());
        for (slot, (method, takes)) in wanted.iter().enumerate() {
            // LR40: a name may have several signatures, and the one filling
            // the slot is the one that takes what the slot takes.
            let found = structure.methods.get(method).and_then(|overloads| {
                let mut fitting = overloads
                    .iter()
                    .filter(|signature| signature.params.len() == *takes);
                let first = fitting.next()?;
                fitting.next().is_none().then_some(first.span)
            });

            let Some((found, throws)) = found
                .and_then(|span| self.functions.get(&span))
                .map(|held| (held.id, held.throws))
            else {
                self.gap(
                    span,
                    format!(
                        "`{name}` implementing `{method}` in a way the compiler cannot resolve"
                    ),
                );
                return;
            };
            if throws
                && let Shape::Interface(held) = &mut self.program.nominal_mut(interface).shape
                && let Some(method) = held.methods.get_mut(slot)
            {
                method.throws = true;
            }
            methods.push(found);
        }

        if let Shape::Interface(held) = &mut self.program.nominal_mut(interface).shape {
            held.implementors.push(Implementation {
                ty: Ty::Named {
                    id: ty,
                    args: Vec::new(),
                },
                methods,
            });
        }
    }

    fn adapt_throwing_virtuals(&mut self) {
        let mut adapters = Vec::new();
        for (interface, nominal) in self.program.types() {
            let Shape::Interface(held) = &nominal.shape else {
                continue;
            };
            for implementation in &held.implementors {
                for (slot, callee) in implementation.methods.iter().copied().enumerate() {
                    if held.methods.get(slot).is_some_and(|method| method.throws) {
                        adapters.push((interface, implementation.ty.clone(), slot, callee));
                    }
                }
            }
        }
        for (interface, ty, slot, callee) in adapters {
            let adapter = self.virtual_adapter(callee);
            let Shape::Interface(held) = &mut self.program.nominal_mut(interface).shape else {
                continue;
            };
            if let Some(method) = held
                .implementors
                .iter_mut()
                .find(|implementation| implementation.ty == ty)
                .and_then(|implementation| implementation.methods.get_mut(slot))
            {
                *method = adapter;
            }
        }
    }

    fn virtual_adapter(&mut self, callee: FuncId) -> FuncId {
        let source = self.program.function(callee).clone();
        let (declared, throws) = match &source.result {
            Ty::Builtin {
                kind: Builtin::Result,
                args,
            } if args.get(1) == Some(&Ty::Dynamic) => {
                (args.first().cloned().unwrap_or(Ty::Unit), true)
            }
            result => (result.clone(), false),
        };
        let index = self.program.functions().count();
        let mut adapter = Function::new(
            format!("{}#virtual{index}", source.name),
            source.params.clone(),
            thrown_or(declared),
            source.span,
        );
        adapter.type_params.clone_from(&source.type_params);
        let entry = adapter.entry;
        let args = adapter.block(entry).params.clone();
        let called = adapter.add_value(source.result.clone());
        adapter.block_mut(entry).insts.push(Inst {
            result: Some(called),
            kind: InstKind::Call {
                callee,
                type_args: source
                    .type_params
                    .iter()
                    .cloned()
                    .map(Ty::Parameter)
                    .collect(),
                args,
            },
            span: source.span,
        });
        let returned = if throws {
            called
        } else {
            let result = adapter.result.clone();
            let returned = adapter.add_value(result.clone());
            adapter.block_mut(entry).insts.push(Inst {
                result: Some(returned),
                kind: InstKind::MakeEnum {
                    ty: result,
                    variant: 0,
                    payload: vec![called],
                },
                span: source.span,
            });
            returned
        };
        adapter.block_mut(entry).term = Some(Terminator::Return(returned));
        self.program.add_function(adapter)
    }

    /// Fills in every declared function's body.
    fn lower_bodies(&mut self) {
        let pending = std::mem::take(&mut self.bodies);
        let mut built = Vec::with_capacity(pending.len());
        let mut made = Vec::new();

        // A closure is a function nothing declared, so it takes an id after
        // every declaration has one (LR9.8).
        let next = Cell::new(
            u32::try_from(self.program.functions().count()).expect("function count fits in u32"),
        );

        for pending in &pending {
            let context = body::Context {
                next_function: &next,
                facts: self.facts,
                mode: self.mode,
                ids: &self.ids,
                callees: &self.functions,
                virtuals: &self.virtuals,
                defaults: &self.defaults,
                properties: &self.properties,
                displays: &self.displays,
                program: &self.program,
                module: pending.module,
                constants: &self.constants,
            };
            let shell = self.program.function(pending.id).clone();
            let (function, closures, gaps) = body::Body::new(context, shell, pending.throws).lower(
                None,
                &pending.bindings,
                &pending.body,
            );
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
        // block extends.
        let table = self.table;
        let Some(Decl::Extension {
            type_params,
            target,
            ..
        }) = table.get(module, owner)
        else {
            return None;
        };
        let target = types::convert(target, &self.ids).ok()?;
        Some((target, type_params.clone()))
    }

    /// Every free function declaration, and every member with a body, with
    /// the path naming it inside its module.
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

    fn repr_c(&self, module: ModuleId, name: &str) -> bool {
        self.graph
            .module(module)
            .ast
            .items
            .iter()
            .find_map(|item| match item {
                Item::Struct(structure) if structure.name == name => {
                    Some(structure.decorators.iter().any(|decorator| {
                        decorator.name == "repr"
                            && matches!(
                                decorator.args.first().map(|argument| &argument.value.kind),
                                Some(luar_ast::ExprKind::String(repr)) if repr == "C"
                            )
                    }))
                }
                _ => None,
            })
            .unwrap_or(false)
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
        // LR75: an enum declares no members, and carries what `@derive` wrote.
        Decl::Enum(enumeration) => enumeration.methods.values().flatten().collect(),
        Decl::Alias { .. } | Decl::Decorator { .. } | Decl::Constant { .. } => Vec::new(),
    }
}

fn collect(items: &[Item], module: ModuleId, found: &mut Vec<(ModuleId, String, AstFunction)>) {
    for item in items {
        match item {
            // LR60: an intrinsic without a runtime symbol is lowered in place
            // at every call.
            Item::Function(function)
                if !is_intrinsic(function) || extern_symbol(function).is_some() =>
            {
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

fn initialization_order(graph: &Graph) -> Vec<ModuleId> {
    fn visit(
        graph: &Graph,
        module: ModuleId,
        seen: &mut HashSet<ModuleId>,
        ordered: &mut Vec<ModuleId>,
    ) {
        if !seen.insert(module) {
            return;
        }
        for dependency in graph
            .module(module)
            .imports
            .iter()
            .filter_map(|edge| edge.target)
        {
            visit(graph, dependency, seen, ordered);
        }
        ordered.push(module);
    }

    let mut seen = HashSet::new();
    let mut ordered = Vec::new();
    for (module, _) in graph.modules() {
        visit(graph, module, &mut seen, &mut ordered);
    }
    ordered
}

fn is_finalizer(function: &AstFunction) -> bool {
    function
        .decorators
        .iter()
        .any(|decorator| decorator.name == "finalizer")
}

fn inline(function: &AstFunction) -> crate::program::Inline {
    if function
        .decorators
        .iter()
        .any(|decorator| decorator.name == "noinline")
    {
        crate::program::Inline::Never
    } else if function
        .decorators
        .iter()
        .any(|decorator| decorator.name == "inline")
    {
        crate::program::Inline::Always
    } else {
        crate::program::Inline::Default
    }
}

fn extern_symbol(function: &AstFunction) -> Option<String> {
    if is_intrinsic(function) {
        let [name] = function.name.as_slice() else {
            return None;
        };
        return runtime_symbol(name).map(str::to_owned);
    }
    function
        .decorators
        .iter()
        .find(|decorator| decorator.name == "extern")
        .and_then(|decorator| decorator.args.first())
        .and_then(|argument| match &argument.value.kind {
            luar_ast::ExprKind::String(abi) if abi == "c" => Some(function.name.join(".")),
            _ => None,
        })
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

fn is_intrinsic(function: &AstFunction) -> bool {
    function
        .decorators
        .iter()
        .any(|decorator| decorator.name == "intrinsic")
}
