//! Resolving names to what binds them (LR54).

use std::collections::HashSet;

use luar_ast::{
    ArmBody, Binding, Block, Expr, ExprKind, Field, Function, FunctionBody, InterpolationPart,
    Item, MapKey, Member, Module, Param, Pattern, PatternKind, Payload, Property, Stmt, StmtKind,
};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::init::Use;
use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin, bound};

/// The names in scope in every module, with no import (LR54.1).
pub static PREDECLARED: &[&str] = &[
    "print",
    "assert",
    "debugAssert",
    "panic",
    "unreachable",
    "Result",
    "Error",
    "List",
    "Map",
    "Set",
];

/// Resolves every name in every module of `graph`.
#[must_use]
pub fn resolve(graph: &Graph, names: &Names) -> (Vec<Diagnostic>, Vec<Use>) {
    let mut diagnostics = Vec::new();
    let mut uses = Vec::new();

    for (id, node) in graph.modules() {
        let mut resolver = Resolver {
            module: names,
            scope: id,
            frames: vec![HashSet::new()],
            initializing: false,
            diagnostics: &mut diagnostics,
            uses: &mut uses,
        };
        resolver.module(&node.ast);
    }

    (diagnostics, uses)
}

struct Resolver<'a> {
    module: &'a Names,
    scope: ModuleId,
    /// Names bound inside the module, innermost last. The first frame holds
    /// the module's own `local` and `const` bindings (LR21.3), which are
    /// visible from where they are written onward, unlike declarations.
    frames: Vec<HashSet<String>>,
    /// Whether the walk is inside the module's top-level code, which runs
    /// before `main` (LR78). A function body runs later, so it is not.
    initializing: bool,
    diagnostics: &'a mut Vec<Diagnostic>,
    uses: &'a mut Vec<Use>,
}

/// What a name resolves to, as far as scope is concerned.
enum Found {
    /// A local, a parameter, a pattern binding, or a module-level binding the
    /// walk has already passed.
    Binding,
    /// A declaration of this module, or a predeclared name (LR54.1).
    Declaration,
    /// A name another module owns, and the module that owns it (LR21.1).
    Other(ModuleId),
    /// Nothing binds it.
    Nothing,
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
            Item::Stmt(stmt) => {
                self.initializing = true;
                self.stmt(stmt);
                self.initializing = false;
            }
        }
    }

    fn member(&mut self, member: &Member) {
        match member {
            Member::Field(Field { default, .. }) => {
                if let Some(default) = default {
                    self.expr(default);
                }
            }
            Member::Function { function, .. } => self.function(function),
            Member::Property(property) => self.property(property),
        }
    }

    /// A property's accessors take no parameters and read `self`, unlike a
    /// method, which declares it (LR43, LR65).
    fn property(&mut self, property: &Property) {
        let outer = std::mem::replace(&mut self.initializing, false);

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

        self.initializing = outer;
    }

    fn function(&mut self, function: &Function) {
        let Some(body) = &function.body else { return };

        // A declared body runs when it is called, which is after every module
        // has initialized (LR78).
        let outer = std::mem::replace(&mut self.initializing, false);
        self.push();
        self.params(&function.params);
        self.block(body);
        self.pop();
        self.initializing = outer;
    }

    /// Parameters, in order. A default may use the parameters before it and
    /// nothing after, which is the order they are written in (LR9.4).
    fn params(&mut self, params: &[Param]) {
        let mut taken: HashSet<String> = HashSet::new();

        for param in params {
            if let Some(default) = &param.default {
                self.expr(default);
            }

            for name in bound(&param.binding) {
                if !taken.insert(name.clone()) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::PARAMETER_REDECLARED,
                            param.span,
                            format!("`{name}` is already a parameter of this function"),
                        )
                        .note("A binding in an inner scope may shadow one, but a parameter list names each parameter once (LR53)."),
                    );
                }
                self.bind(&name);
            }
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
            // `local x = x` reads the outer `x` (LR54).
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
            // scope rather than after it (LR10.3).
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
            StmtKind::Unsafe(body) => self.block(body),
            // LR26: what is deferred is written here and runs on the way out,
            // so its names are the ones in scope where it is written.
            StmtKind::Defer(deferred) => self.expr(deferred),
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
            StmtKind::Throw(value) => self.expr(value),
            // LR25.3: a clause binds the caught value for its own block.
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                self.block(body);
                for clause in catches {
                    self.push();
                    self.bind(&clause.name);
                    self.block(&clause.body);
                    self.pop();
                }
                if let Some(finally) = finally {
                    self.block(finally);
                }
            }
            StmtKind::Expr(expr) => self.expr(expr),
        }
    }

    /// What an assignment writes to (LR5.4).
    fn assigned(&mut self, target: &Expr) {
        match &target.kind {
            ExprKind::Name(name) => {
                if matches!(self.find(name), Found::Nothing) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::IMPLICIT_GLOBAL,
                            target.span,
                            format!(
                                "`{name}` is not declared, and assigning to it declares nothing"
                            ),
                        )
                        .note("Module-level state is declared with `local` or `const` (LR52)."),
                    );
                }
            }
            _ => self.expr(target),
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Name(name) => self.read(name, expr.span),
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
            ExprKind::Try(inner) | ExprKind::Await(inner) => self.expr(inner),
            ExprKind::Cast { value, .. } | ExprKind::TypeTest { value, .. } => self.expr(value),
            ExprKind::AddressOf { operand, .. } => self.expr(operand),
            ExprKind::Tuple(items) | ExprKind::List(items) | ExprKind::Set(items) => {
                for item in items {
                    self.expr(item);
                }
            }
            // The path names the type being built, which is resolved with the
            // types (LR12.2).
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
    /// (LR16.2).
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

    /// Binds what a binding binds (LR5.3).
    fn binding(&mut self, binding: &Binding) {
        for name in bound(binding) {
            self.bind(&name);
        }
    }

    /// What binds `name` where it is written.
    fn find(&self, name: &str) -> Found {
        if self.frames.iter().any(|frame| frame.contains(name)) {
            return Found::Binding;
        }

        match self.module.scope(self.scope).get(name).map(|b| &b.origin) {
            Some(Origin::Declared { .. }) => Found::Declaration,
            Some(Origin::Imported { module, .. } | Origin::Namespace(module)) => {
                Found::Other(*module)
            }
            Some(Origin::Binding { .. }) | None => {
                if PREDECLARED.contains(&name) {
                    Found::Declaration
                } else {
                    Found::Nothing
                }
            }
        }
    }

    /// Reads `name`, recording it where it reaches another module while this
    /// one is initializing (LR78).
    fn read(&mut self, name: &str, span: Span) {
        match self.find(name) {
            Found::Binding | Found::Declaration => {}
            Found::Other(module) => {
                if self.initializing {
                    self.uses.push(Use {
                        module: self.scope,
                        needs: module,
                        span,
                    });
                }
            }
            Found::Nothing => self.not_in_scope(name, span),
        }
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
