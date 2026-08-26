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

use std::collections::HashMap;

use luar_ast::{
    ArmBody, BinaryOp, Binding, Block, Expr, ExprKind, Function, FunctionBody, InterpolationPart,
    Item, MapKey, MatchArm, Member, Module, Param, Pattern, PatternKind, Payload, Property, Stmt,
    StmtKind, Struct, UnaryOp,
};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::annotations::Resolver;
use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin, bound};
use crate::table::{Decl, Field, Signature, Table};
use crate::types::{Builtin, Primitive, Type};

/// Checks the types of every module in `graph`.
#[must_use]
pub fn check(graph: &Graph, names: &Names, table: &Table) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    for (id, node) in graph.modules() {
        let mut checker = Checker {
            names,
            table,
            types: Resolver::new(names, table.kinds(), id),
            scope: id,
            values: vec![HashMap::new()],
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
            // A declaration the table holds was resolved when the table was
            // built, so its body is checked against what is recorded there.
            Item::Function(function) => {
                let signature = match function.name.as_slice() {
                    [name] => self.table.signature(self.scope, name).cloned(),
                    _ => None,
                };
                self.body(function, signature.as_ref(), None);
            }
            Item::Struct(structure) => self.structure(structure),
            Item::Extend(extend) => {
                let methods = match self.table.get(self.scope, &extend.name) {
                    Some(Decl::Extension { methods, .. }) => methods.clone(),
                    _ => Default::default(),
                };
                for function in &extend.functions {
                    let signature = function.name.last().and_then(|name| methods.get(name));
                    self.body(function, signature, None);
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

    fn structure(&mut self, structure: &Struct) {
        let Some(declared) = self.table.structure(self.scope, &structure.name).cloned() else {
            return;
        };

        // LR65: `self` in a member is the type the member is declared in.
        let receiver = Type::Named {
            module: self.scope,
            name: structure.name.clone(),
            args: structure
                .type_params
                .iter()
                .map(|param| Type::Parameter(param.clone()))
                .collect(),
        };

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
                Member::Function(function) => {
                    let signature = function
                        .name
                        .last()
                        .and_then(|name| declared.methods.get(name))
                        .cloned();
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
        self.push();
        self.bind("self", receiver.clone());
        self.block(&property.get);
        self.pop();

        if let Some(setter) = &property.set {
            self.push();
            self.bind("self", receiver);
            self.bind(&setter.param, held);
            self.block(&setter.body);
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

        let offset = usize::from(signature.is_some_and(|signature| signature.takes_self));
        for (index, param) in function.params.iter().enumerate() {
            let declared = match signature {
                Some(signature) => index
                    .checked_sub(offset)
                    .and_then(|index| signature.params.get(index))
                    .map_or(Type::Unresolved, |param| param.ty.clone()),
                None => match &param.ty {
                    Some(ty) => self.resolve(ty),
                    None => Type::Unresolved,
                },
            };
            self.param(param, declared);
        }

        if signature.is_none() {
            if let Some(result) = &function.result {
                self.resolve(result);
            }
        }

        if let Some(body) = &function.body {
            for stmt in &body.stmts {
                self.stmt(stmt);
            }
        }

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
                let wanted = self.expr(target);
                let held = self.expr(value);
                self.expect(&wanted, &held, value.span);
            }
            StmtKind::If {
                branches,
                otherwise,
            } => {
                for branch in branches {
                    self.condition(&branch.condition);
                    self.block(&branch.body);
                }
                if let Some(otherwise) = otherwise {
                    self.block(otherwise);
                }
            }
            StmtKind::While {
                condition, body, ..
            } => {
                self.condition(condition);
                self.block(body);
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
            StmtKind::Expr(expr) => {
                self.expr(expr);
            }
            StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Error => {}
        }
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
                for arg in args {
                    self.expr(&arg.value);
                }
                self.returns(callee, method.as_deref(), &receiver)
            }
            ExprKind::Field {
                receiver,
                name,
                optional,
            } => {
                let held = self.expr(receiver);
                let member = self.member(&held, name, expr.span);

                // Reaching through `?.` gives nothing where the receiver is
                // absent, so the result is optional too (LR8).
                if *optional {
                    Type::Optional(Box::new(member))
                } else {
                    member
                }
            }
            ExprKind::Index {
                receiver, index, ..
            } => {
                self.expr(receiver);
                self.expr(index);
                Type::Unresolved
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
                let mut members = Vec::with_capacity(fields.len());
                for field in fields {
                    let value = settle(self.expr(&field.value));
                    members.push((field.name.clone(), value));
                }

                // LR12.2: a path names the type being built. Without one the
                // literal is a structural record (LR12.1).
                if path.is_empty() {
                    Type::Record(members)
                } else {
                    self.types
                        .named(path, Vec::new())
                        .unwrap_or(Type::Unresolved)
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
                self.pop();

                Type::Function {
                    asynchronous: *asynchronous,
                    params: types,
                    result: Box::new(returns),
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                for arm in arms {
                    self.arm(arm);
                }
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
        let Type::Named {
            module,
            name: declared,
            ..
        } = held
        else {
            return Type::Unresolved;
        };
        let Some(structure) = self.table.structure(*module, declared) else {
            return Type::Unresolved;
        };

        if let Some(field) = structure.fields.iter().find(|field| field.name == name) {
            return field.ty.clone();
        }
        if let Some(property) = structure.properties.iter().find(|field| field.name == name) {
            return property.ty.clone();
        }

        // LR89.1: `:` calls a method and `.` reaches fields, and neither
        // spelling is a fallback for the other.
        let mut reported = Diagnostic::error(
            codes::NO_SUCH_MEMBER,
            span,
            format!("`{declared}` has no member `{name}`"),
        );
        if structure.methods.contains_key(name) {
            reported = reported.note(format!(
                "`{name}` is a method, and a method is called with `:` (LR12.2)."
            ));
        }
        self.diagnostics.push(reported);

        Type::Unresolved
    }

    /// What a call gives back: the result of the method being called, or of
    /// the function the callee names.
    fn returns(&mut self, callee: &Expr, method: Option<&str>, receiver: &Type) -> Type {
        if let Some(method) = method {
            let Type::Named { module, name, .. } = receiver else {
                return Type::Unresolved;
            };
            return match self.table.structure(*module, name) {
                Some(structure) => structure
                    .methods
                    .get(method)
                    .map_or(Type::Unresolved, |signature| signature.result.clone()),
                None => Type::Unresolved,
            };
        }

        // A call through anything but a plain name reaches a value whose type
        // this stage does not follow yet.
        let ExprKind::Name(name) = &callee.kind else {
            return Type::Unresolved;
        };

        // A local holding a function shadows a declaration of the same name.
        if self
            .values
            .iter()
            .rev()
            .any(|scope| scope.contains_key(name))
        {
            return Type::Unresolved;
        }

        let declared = match self.names.scope(self.scope).get(name).map(|b| &b.origin) {
            Some(Origin::Declared { .. }) => Some((self.scope, name.clone())),
            Some(Origin::Imported { module, name }) => Some((*module, name.clone())),
            _ => None,
        };

        match declared {
            Some((module, name)) => self
                .table
                .signature(module, &name)
                .map_or(Type::Unresolved, |signature| signature.result.clone()),
            None => Type::Unresolved,
        }
    }

    fn name(&mut self, name: &str) -> Type {
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
        let held_right = self.expr(right);

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
        if wanted.accepts(held) {
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
