//! Resolving names to what binds them (§54).
//!
//! A name in value position must name something: a local, a parameter, a
//! pattern binding, a declaration in this module, an import, or one of the
//! predeclared names (§54.1). One that names nothing is reported here.
//!
//! Scopes nest. Blocks, function bodies, loop bodies, and match arms each
//! open one, and a binding is visible from where it is written to the end of
//! the scope holding it. That is what makes `local value = 10` inside an `if`
//! invisible after the `end`, and what lets an inner binding shadow an outer
//! one (§53).
//!
//! Names in type position are not resolved here. Types are checked in their
//! own stage, and resolving them twice, in two places, with two different
//! ideas of what is in scope, is how the two come to disagree.

use std::collections::HashSet;

use luar_ast::{
    ArmBody, Binding, Block, Expr, ExprKind, Field, Function, FunctionBody, InterpolationPart,
    Item, MapKey, Member, Module, Param, Pattern, PatternKind, Payload, Property, Stmt, StmtKind,
};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::modules::Graph;
use crate::names::Names;

/// The names in scope in every module, with no import (§54.1).
///
/// A declaration or an import of the same name shadows one, which is why the
/// module's own names are searched first.
pub static PREDECLARED: &[&str] = &[
    "print",
    "assert",
    "debugAssert",
    "panic",
    "unreachable",
    "Result",
];

/// Resolves every name in every module of `graph`.
#[must_use]
pub fn resolve(graph: &Graph, names: &Names) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    for (id, node) in graph.modules() {
        let mut resolver = Resolver {
            module: names,
            scope: id,
            frames: vec![HashSet::new()],
            diagnostics: &mut diagnostics,
        };
        resolver.module(&node.ast);
    }

    diagnostics
}

struct Resolver<'a> {
    module: &'a Names,
    scope: crate::modules::ModuleId,
    /// Names bound inside the module, innermost last. The first frame holds
    /// the module's own `local` and `const` bindings (§21.3), which are
    /// visible from where they are written onward, unlike declarations.
    frames: Vec<HashSet<String>>,
    diagnostics: &'a mut Vec<Diagnostic>,
}

impl Resolver<'_> {
    fn module(&mut self, module: &Module) {
        for item in &module.items {
            self.item(item);
        }
    }

    fn item(&mut self, item: &Item) {
        match item {
            // Bound already, by the pass that reads what each module exports.
            Item::Import(_) => {}
            Item::Function(function) => self.function(function),
            Item::Struct(structure) => {
                for member in &structure.members {
                    self.member(member);
                }
            }
            Item::Extend(extend) => {
                for function in &extend.functions {
                    self.function(function);
                }
            }
            // A declaration with no body of its own: an enum's payloads, an
            // interface's signatures, and an alias are types.
            Item::Enum(_) | Item::Interface(_) | Item::TypeAlias(_) => {}
            Item::Conditional(conditional) => {
                // §48 conditions test the target, not anything in scope here.
                for (_, items) in &conditional.branches {
                    for item in items {
                        self.item(item);
                    }
                }
                for item in conditional.otherwise.iter().flatten() {
                    self.item(item);
                }
            }
            Item::Stmt(stmt) => self.stmt(stmt),
        }
    }

    fn member(&mut self, member: &Member) {
        match member {
            Member::Field(Field { default, .. }) => {
                if let Some(default) = default {
                    self.expr(default);
                }
            }
            Member::Function(function) => self.function(function),
            Member::Property(property) => self.property(property),
        }
    }

    /// A property's accessors take no parameters and read `self`, unlike a
    /// method, which declares it (§43, §65).
    fn property(&mut self, property: &Property) {
        self.push();
        self.bind("self");
        self.block(&property.get);
        self.pop();

        if let Some(setter) = &property.set {
            self.push();
            self.bind("self");
            self.bind(&setter.param);
            self.block(&setter.body);
            self.pop();
        }
    }

    fn function(&mut self, function: &Function) {
        let Some(body) = &function.body else { return };

        self.push();
        self.params(&function.params);
        self.block(body);
        self.pop();
    }

    /// Parameters, in order. A default may use the parameters before it and
    /// nothing after, which is the order they are written in (§9.4).
    fn params(&mut self, params: &[Param]) {
        for param in params {
            if let Some(default) = &param.default {
                self.expr(default);
            }
            self.binding(&param.binding);
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
            // The value is read where the binding is not yet in scope, so
            // `local x = x` reads the outer `x` (§54).
            StmtKind::Local { binding, value, .. } => {
                if let Some(value) = value {
                    self.expr(value);
                }
                self.binding(binding);
            }
            StmtKind::Const { binding, value, .. } => {
                self.expr(value);
                self.binding(binding);
            }
            StmtKind::Assign { target, value, .. } => {
                self.expr(value);
                self.assigned(target);
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
            // `until` reads the body's bindings, so it is inside the body's
            // scope rather than after it (§10.3).
            StmtKind::Repeat { body, until, .. } => {
                self.push();
                for stmt in &body.stmts {
                    self.stmt(stmt);
                }
                self.expr(until);
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
                    self.binding(binding);
                }
                self.block(body);
                self.pop();
            }
            StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Error => {}
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
                    self.push();
                    self.pattern(&arm.pattern);
                    if let Some(guard) = &arm.guard {
                        self.expr(guard);
                    }
                    match &arm.body {
                        ArmBody::Block(block) => self.block(block),
                        ArmBody::Expr(expr) => self.expr(expr),
                    }
                    self.pop();
                }
            }
            StmtKind::Return(value) => {
                if let Some(value) = value {
                    self.expr(value);
                }
            }
            StmtKind::Expr(expr) => self.expr(expr),
        }
    }

    /// What an assignment writes to (§5.4).
    ///
    /// Assigning to a name declares nothing: §52 forbids creating a variable
    /// by writing to it, so a name that is not already in scope is that rule
    /// rather than an unknown name. Everything else is an ordinary read of
    /// the thing being written into.
    fn assigned(&mut self, target: &Expr) {
        match &target.kind {
            ExprKind::Name(name) => {
                if !self.in_scope(name) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::IMPLICIT_GLOBAL,
                            target.span,
                            format!(
                                "`{name}` is not declared, and assigning to it declares nothing"
                            ),
                        )
                        .note("Module-level state is declared with `local` or `const` (§52)."),
                    );
                }
            }
            _ => self.expr(target),
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Name(name) => {
                if !self.in_scope(name) {
                    self.not_in_scope(name, expr.span);
                }
            }
            ExprKind::Nil
            | ExprKind::Bool(_)
            | ExprKind::Integer(_)
            | ExprKind::Float(_)
            | ExprKind::String(_)
            | ExprKind::ByteString(_)
            | ExprKind::Char(_)
            | ExprKind::Error => {}
            ExprKind::Interpolation(parts) => {
                for part in parts {
                    if let InterpolationPart::Expr(expr) = part {
                        self.expr(expr);
                    }
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
            ExprKind::Call { callee, args, .. } => {
                self.expr(callee);
                for arg in args {
                    self.expr(&arg.value);
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
            ExprKind::Cast { value, .. } | ExprKind::TypeTest { value, .. } => self.expr(value),
            ExprKind::AddressOf { operand, .. } => self.expr(operand),
            ExprKind::Tuple(items) | ExprKind::List(items) => {
                for item in items {
                    self.expr(item);
                }
            }
            // The path names the type being built, which is resolved with the
            // types (§12.2).
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
            ExprKind::Function { params, body, .. } => {
                self.push();
                self.params(params);
                match body.as_ref() {
                    FunctionBody::Block(block) => self.block(block),
                    FunctionBody::Expr(expr) => self.expr(expr),
                }
                self.pop();
            }
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                for arm in arms {
                    self.push();
                    self.pattern(&arm.pattern);
                    if let Some(guard) = &arm.guard {
                        self.expr(guard);
                    }
                    match &arm.body {
                        ArmBody::Block(block) => self.block(block),
                        ArmBody::Expr(expr) => self.expr(expr),
                    }
                    self.pop();
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
        }
    }

    /// Binds what a pattern binds, and reads the literals it matches against
    /// (§16.2).
    ///
    /// A path names an enum variant, a struct, or a record type, and is
    /// resolved with the types.
    fn pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Error => {}
            PatternKind::Binding(name) => self.bind(name),
            PatternKind::Literal(literal) => self.expr(literal),
            PatternKind::Range { start, end, .. } => {
                self.expr(start);
                self.expr(end);
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
                            None => self.bind(field.bound_as.as_ref().unwrap_or(&field.field)),
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
                    self.bind(name);
                }
            }
            PatternKind::Tuple(patterns) | PatternKind::Or(patterns) => {
                for pattern in patterns {
                    self.pattern(pattern);
                }
            }
            PatternKind::Typed { inner, .. } => self.pattern(inner),
        }
    }

    /// Binds what a binding binds (§5.3).
    fn binding(&mut self, binding: &Binding) {
        match binding {
            Binding::Name(name) => self.bind(name),
            Binding::Record(fields) => {
                for field in fields {
                    self.bind(field.bound_as.as_ref().unwrap_or(&field.field));
                }
            }
            Binding::Tuple(bindings) => {
                for binding in bindings {
                    self.binding(binding);
                }
            }
            Binding::Error => {}
        }
    }

    fn in_scope(&self, name: &str) -> bool {
        self.frames.iter().any(|frame| frame.contains(name))
            || self.module.scope(self.scope).get(name).is_some()
            || PREDECLARED.contains(&name)
    }

    fn bind(&mut self, name: &str) {
        self.frames
            .last_mut()
            .expect("a frame is open")
            .insert(name.to_owned());
    }

    fn push(&mut self) {
        self.frames.push(HashSet::new());
    }

    fn pop(&mut self) {
        self.frames.pop();
    }

    fn not_in_scope(&mut self, name: &str, span: Span) {
        self.diagnostics.push(Diagnostic::error(
            codes::NAME_NOT_IN_SCOPE,
            span,
            format!("`{name}` is not in scope"),
        ));
    }
}
