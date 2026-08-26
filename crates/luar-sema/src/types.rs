//! Types: what the spellings mean, and whether a written type names anything
//! (§4.3, §6, §54).
//!
//! A type annotation is checked here the way a name is checked in value
//! position: every path in it must name a primitive, a collection the
//! language builds itself, a type parameter of the enclosing declaration, a
//! declaration of this module, or an import.
//!
//! What a type *is* comes later, with the checking that compares them. This
//! is the part that decides whether the words were words at all.

use std::collections::HashSet;

use luar_ast::{Function, Item, Member, Module, Param, Struct, Type, TypeKind};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin};

/// A primitive type (§6).
///
/// `int`, `uint`, and `float` are spellings of `i64`, `u64`, and `f64`
/// (§4.3, §4.4): the same type under two names, on every target. `isize` and
/// `usize` are distinct types, and exist for FFI and allocator code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Primitive {
    Nil,
    Bool,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    Isize,
    Usize,
    F32,
    F64,
    String,
    Bytes,
    Char,
    Never,
    Any,
    Unknown,
}

impl Primitive {
    /// The primitive `name` spells, if it spells one.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        let primitive = match name {
            "nil" => Self::Nil,
            "bool" => Self::Bool,
            "i8" => Self::I8,
            "i16" => Self::I16,
            "i32" => Self::I32,
            "i64" | "int" => Self::I64,
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" | "uint" => Self::U64,
            "isize" => Self::Isize,
            "usize" => Self::Usize,
            "f32" => Self::F32,
            "f64" | "float" => Self::F64,
            "string" => Self::String,
            "bytes" => Self::Bytes,
            "char" => Self::Char,
            "never" => Self::Never,
            "any" => Self::Any,
            "unknown" => Self::Unknown,
            _ => return None,
        };
        Some(primitive)
    }

    /// How a diagnostic spells it. `int` reads as `int` rather than `i64`,
    /// because that is the name the spec gives the default (§4.3).
    #[must_use]
    pub fn spelling(self) -> &'static str {
        match self {
            Self::Nil => "nil",
            Self::Bool => "bool",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "int",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "uint",
            Self::Isize => "isize",
            Self::Usize => "usize",
            Self::F32 => "f32",
            Self::F64 => "float",
            Self::String => "string",
            Self::Bytes => "bytes",
            Self::Char => "char",
            Self::Never => "never",
            Self::Any => "any",
            Self::Unknown => "unknown",
        }
    }
}

/// A generic type the language names without an import (§54.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Builtin {
    /// `Result<T, E>`, the type of every fallible signature (§25.1).
    Result,
    /// The collections `[...]` and `Map { ... }` build (§13).
    List,
    Map,
    Set,
    /// What freezing one returns (§59).
    FrozenList,
    FrozenMap,
    FrozenSet,
}

impl Builtin {
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        let builtin = match name {
            "Result" => Self::Result,
            "List" => Self::List,
            "Map" => Self::Map,
            "Set" => Self::Set,
            "FrozenList" => Self::FrozenList,
            "FrozenMap" => Self::FrozenMap,
            "FrozenSet" => Self::FrozenSet,
            _ => return None,
        };
        Some(builtin)
    }
}

/// Checks every type written in every module of `graph`.
#[must_use]
pub fn check(graph: &Graph, names: &Names) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    for (id, node) in graph.modules() {
        let mut checker = Checker {
            module: names,
            scope: id,
            parameters: Vec::new(),
            diagnostics: &mut diagnostics,
        };
        checker.module(&node.ast);
    }

    diagnostics
}

struct Checker<'a> {
    module: &'a Names,
    scope: ModuleId,
    /// The type parameters of the declarations being walked, innermost last
    /// (§19).
    parameters: Vec<HashSet<String>>,
    diagnostics: &'a mut Vec<Diagnostic>,
}

impl Checker<'_> {
    fn module(&mut self, module: &Module) {
        for item in &module.items {
            self.item(item);
        }
    }

    fn item(&mut self, item: &Item) {
        match item {
            Item::Function(function) => self.function(function),
            Item::Struct(structure) => self.structure(structure),
            Item::Enum(enumeration) => {
                self.push(&enumeration.type_params);
                for variant in &enumeration.variants {
                    match &variant.payload {
                        None => {}
                        Some(luar_ast::VariantPayload::Tuple(types)) => {
                            for ty in types {
                                self.ty(ty);
                            }
                        }
                        Some(luar_ast::VariantPayload::Record(fields)) => {
                            for field in fields {
                                self.ty(&field.ty);
                            }
                        }
                    }
                }
                self.pop();
            }
            Item::Interface(interface) => {
                self.push(&interface.type_params);
                for member in &interface.members {
                    match member {
                        luar_ast::InterfaceMember::Function(function) => self.function(function),
                        luar_ast::InterfaceMember::Property { ty, .. } => self.ty(ty),
                    }
                }
                self.pop();
            }
            Item::Extend(extend) => {
                self.ty(&extend.target);
                for function in &extend.functions {
                    self.function(function);
                }
            }
            Item::TypeAlias(alias) => {
                self.push(&alias.type_params);
                self.ty(&alias.target);
                self.pop();
            }
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

    fn structure(&mut self, structure: &Struct) {
        self.push(&structure.type_params);

        for implemented in &structure.implements {
            self.ty(implemented);
        }

        for member in &structure.members {
            match member {
                Member::Field(field) => self.ty(&field.ty),
                Member::Function(function) => self.function(function),
                Member::Property(property) => self.ty(&property.ty),
            }
        }

        self.pop();
    }

    fn function(&mut self, function: &Function) {
        self.push(&function.type_params);

        for param in &function.params {
            self.param(param);
        }
        if let Some(result) = &function.result {
            self.ty(result);
        }
        if let Some(body) = &function.body {
            self.block(body);
        }

        self.pop();
    }

    fn param(&mut self, param: &Param) {
        if let Some(ty) = &param.ty {
            self.ty(ty);
        }
    }

    fn block(&mut self, block: &luar_ast::Block) {
        for stmt in &block.stmts {
            self.stmt(stmt);
        }
    }

    /// Types written inside a statement: the annotation on a binding, and the
    /// ones a nested block or expression carries.
    fn stmt(&mut self, stmt: &luar_ast::Stmt) {
        use luar_ast::StmtKind;

        match &stmt.kind {
            StmtKind::Local { ty, value, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                if let Some(value) = value {
                    self.expr(value);
                }
            }
            StmtKind::Const { ty, value, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                self.expr(value);
            }
            StmtKind::Assign { target, value, .. } => {
                self.expr(target);
                self.expr(value);
            }
            StmtKind::If {
                branches,
                otherwise,
            } => {
                for branch in branches {
                    self.expr(&branch.condition);
                    self.block(&branch.body);
                }
                if let Some(otherwise) = otherwise {
                    self.block(otherwise);
                }
            }
            StmtKind::While {
                condition, body, ..
            } => {
                self.expr(condition);
                self.block(body);
            }
            StmtKind::Repeat { body, until, .. } => {
                self.block(body);
                self.expr(until);
            }
            StmtKind::For { iterable, body, .. } => {
                self.expr(iterable);
                self.block(body);
            }
            StmtKind::Conditional {
                branches,
                otherwise,
            } => {
                for (_, body) in branches {
                    self.block(body);
                }
                if let Some(otherwise) = otherwise {
                    self.block(otherwise);
                }
            }
            StmtKind::Unsafe(body) => self.block(body),
            StmtKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                for arm in arms {
                    self.arm(arm);
                }
            }
            StmtKind::Return(value) => {
                if let Some(value) = value {
                    self.expr(value);
                }
            }
            StmtKind::Expr(expr) => self.expr(expr),
            StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Error => {}
        }
    }

    fn arm(&mut self, arm: &luar_ast::MatchArm) {
        self.pattern(&arm.pattern);
        if let Some(guard) = &arm.guard {
            self.expr(guard);
        }
        match &arm.body {
            luar_ast::ArmBody::Block(block) => self.block(block),
            luar_ast::ArmBody::Expr(expr) => self.expr(expr),
        }
    }

    /// `value is string` writes a type inside a pattern (§57).
    fn pattern(&mut self, pattern: &luar_ast::Pattern) {
        use luar_ast::{PatternKind, Payload};

        match &pattern.kind {
            PatternKind::Typed { inner, ty } => {
                self.ty(ty);
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
                        if let Some(pattern) = &field.pattern {
                            self.pattern(pattern);
                        }
                    }
                }
            },
            PatternKind::Sequence { before, after, .. } => {
                for pattern in before.iter().chain(after) {
                    self.pattern(pattern);
                }
            }
            PatternKind::Tuple(patterns) | PatternKind::Or(patterns) => {
                for pattern in patterns {
                    self.pattern(pattern);
                }
            }
            PatternKind::Wildcard
            | PatternKind::Binding(_)
            | PatternKind::Literal(_)
            | PatternKind::Range { .. }
            | PatternKind::Error => {}
        }
    }

    /// Types written inside an expression: `x as T`, `x is T`, a call's type
    /// arguments, and the signature of a closure.
    fn expr(&mut self, expr: &luar_ast::Expr) {
        use luar_ast::{ExprKind, FunctionBody, InterpolationPart, MapKey};

        match &expr.kind {
            ExprKind::Cast { value, ty } | ExprKind::TypeTest { value, ty } => {
                self.ty(ty);
                self.expr(value);
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
                ..
            } => {
                for ty in type_args {
                    self.ty(ty);
                }
                self.expr(callee);
                for arg in args {
                    self.expr(&arg.value);
                }
            }
            ExprKind::Function {
                params,
                result,
                body,
                ..
            } => {
                for param in params {
                    self.param(param);
                }
                if let Some(result) = result {
                    self.ty(result);
                }
                match body.as_ref() {
                    FunctionBody::Block(block) => self.block(block),
                    FunctionBody::Expr(expr) => self.expr(expr),
                }
            }
            ExprKind::Unary { operand, .. } => self.expr(operand),
            ExprKind::Binary { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Range { start, end, .. } => {
                for bound in [start, end].into_iter().flatten() {
                    self.expr(bound);
                }
            }
            ExprKind::Field { receiver, .. } => self.expr(receiver),
            ExprKind::Index {
                receiver, index, ..
            } => {
                self.expr(receiver);
                self.expr(index);
            }
            ExprKind::Try(inner) => self.expr(inner),
            ExprKind::AddressOf { operand, .. } => self.expr(operand),
            ExprKind::Tuple(items) | ExprKind::List(items) => {
                for item in items {
                    self.expr(item);
                }
            }
            ExprKind::Record { fields, .. } => {
                for field in fields {
                    self.expr(&field.value);
                }
            }
            ExprKind::Map(entries) => {
                for entry in entries {
                    if let MapKey::Computed(key) = &entry.key {
                        self.expr(key);
                    }
                    self.expr(&entry.value);
                }
            }
            ExprKind::Interpolation(parts) => {
                for part in parts {
                    if let InterpolationPart::Expr(expr) = part {
                        self.expr(expr);
                    }
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                for arm in arms {
                    self.arm(arm);
                }
            }
            ExprKind::If {
                branches,
                otherwise,
            } => {
                for (condition, value) in branches {
                    self.expr(condition);
                    self.expr(value);
                }
                self.expr(otherwise);
            }
            ExprKind::Nil
            | ExprKind::Bool(_)
            | ExprKind::Integer(_)
            | ExprKind::Float(_)
            | ExprKind::String(_)
            | ExprKind::ByteString(_)
            | ExprKind::Char(_)
            | ExprKind::Name(_)
            | ExprKind::Error => {}
        }
    }

    /// One written type, and everything inside it.
    fn ty(&mut self, ty: &Type) {
        match &ty.kind {
            TypeKind::Path { segments, args } => {
                self.path(segments, ty.span);
                for arg in args {
                    self.ty(arg);
                }
            }
            TypeKind::Optional(inner) | TypeKind::Pointer { target: inner, .. } => self.ty(inner),
            TypeKind::Union(members)
            | TypeKind::Intersection(members)
            | TypeKind::Tuple(members) => {
                for member in members {
                    self.ty(member);
                }
            }
            TypeKind::Function { params, result, .. } => {
                for param in params {
                    self.ty(param);
                }
                self.ty(result);
            }
            TypeKind::Array { element, .. } => self.ty(element),
            TypeKind::Record(fields) => {
                for field in fields {
                    self.ty(&field.ty);
                }
            }
            TypeKind::Error => {}
        }
    }

    /// Whether a path names a type.
    ///
    /// A qualified path reaches into another module, and only the module part
    /// is checked here: which of its names are types is decided with the rest
    /// of the type table.
    fn path(&mut self, segments: &[String], span: Span) {
        let Some(name) = segments.first() else { return };

        if Primitive::from_name(name).is_some() || Builtin::from_name(name).is_some() {
            return;
        }

        if self.parameters.iter().any(|scope| scope.contains(name)) {
            return;
        }

        match self.module.scope(self.scope).get(name).map(|b| &b.origin) {
            Some(Origin::Declared { .. } | Origin::Imported { .. } | Origin::Namespace(_)) => {}
            // A module-level value is a value, whatever it is called.
            Some(Origin::Binding { .. }) | None => {
                self.diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_TYPE,
                    span,
                    format!("`{name}` does not name a type"),
                ));
            }
        }
    }

    fn push(&mut self, parameters: &[String]) {
        self.parameters.push(parameters.iter().cloned().collect());
    }

    fn pop(&mut self) {
        self.parameters.pop();
    }
}
