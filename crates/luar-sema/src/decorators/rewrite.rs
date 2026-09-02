//! Rewriting a generated body: captured values are spliced in, and every
//! span moves to the file the body was given (LR23.1).

use std::collections::BTreeMap;

use luar_ast::{
    Argument, ArmBody, Binding, Block, Expr, ExprKind, FieldInit, FunctionBody, InterpolationPart,
    MapKey, Param, Pattern, PatternKind, Payload, Stmt, StmtKind, Type, TypeKind,
};
use luar_diagnostics::{FileId, Span};

use super::Value;

pub(super) struct Rewrite<'a> {
    values: &'a BTreeMap<String, Value>,
    file: FileId,
    /// The next offset past the file's text, for a node with no source of
    /// its own.
    next: u32,
    shadowed: Vec<Vec<String>>,
    pub(super) errors: Vec<(Span, String)>,
}

impl<'a> Rewrite<'a> {
    pub(super) fn new(
        values: &'a BTreeMap<String, Value>,
        file: FileId,
        text_len: u32,
        params: &[Param],
    ) -> Self {
        let mut names = Vec::new();
        for param in params {
            binding_names(&param.binding, &mut names);
        }
        Self {
            values,
            file,
            next: text_len,
            shadowed: vec![names],
            errors: Vec::new(),
        }
    }

    pub(super) fn function(
        &mut self,
        params: &mut [Param],
        result: Option<&mut Type>,
        body: &mut FunctionBody,
    ) {
        for param in params.iter_mut() {
            self.span(&mut param.span);
            self.binding(&mut param.binding);
            if let Some(ty) = &mut param.ty {
                self.ty(ty);
            }
            if let Some(default) = &mut param.default {
                self.expr(default);
            }
        }
        if let Some(result) = result {
            self.ty(result);
        }
        self.body(body);
    }

    fn span(&self, span: &mut Span) {
        span.file = self.file;
    }

    fn fresh(&mut self) -> Span {
        let span = Span::at(self.file, self.next);
        self.next += 1;
        span
    }

    fn body(&mut self, body: &mut FunctionBody) {
        match body {
            FunctionBody::Block(block) => self.block(block),
            FunctionBody::Expr(expression) => self.expr(expression),
        }
    }

    fn block(&mut self, block: &mut Block) {
        self.span(&mut block.span);
        self.shadowed.push(Vec::new());
        for statement in &mut block.stmts {
            self.stmt(statement);
        }
        self.shadowed.pop();
    }

    fn stmt(&mut self, statement: &mut Stmt) {
        self.span(&mut statement.span);
        match &mut statement.kind {
            StmtKind::Local { binding, ty, value } => {
                if let Some(value) = value {
                    self.expr(value);
                }
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                self.declare(binding);
            }
            StmtKind::Const {
                binding, ty, value, ..
            } => {
                self.expr(value);
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                self.declare(binding);
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
                    self.expr(&mut branch.condition);
                    self.block(&mut branch.body);
                }
                if let Some(block) = otherwise {
                    self.block(block);
                }
            }
            StmtKind::While {
                condition, body, ..
            } => {
                self.expr(condition);
                self.block(body);
            }
            StmtKind::Repeat { body, until, .. } => {
                self.span(&mut body.span);
                self.shadowed.push(Vec::new());
                for statement in &mut body.stmts {
                    self.stmt(statement);
                }
                self.expr(until);
                self.shadowed.pop();
            }
            StmtKind::For {
                bindings,
                iterable,
                body,
                ..
            } => {
                self.expr(iterable);
                self.shadowed.push(Vec::new());
                for binding in bindings {
                    self.declare(binding);
                }
                self.block(body);
                self.shadowed.pop();
            }
            StmtKind::Unsafe(block) => self.block(block),
            StmtKind::Defer(expression)
            | StmtKind::Throw(expression)
            | StmtKind::Expr(expression)
            | StmtKind::Return(Some(expression)) => self.expr(expression),
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                self.block(body);
                for clause in catches {
                    self.span(&mut clause.span);
                    if let Some(ty) = &mut clause.ty {
                        self.ty(ty);
                    }
                    self.shadowed.push(vec![clause.name.clone()]);
                    self.block(&mut clause.body);
                    self.shadowed.pop();
                }
                if let Some(block) = finally {
                    self.block(block);
                }
            }
            StmtKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                for arm in arms {
                    self.span(&mut arm.span);
                    self.arm(&mut arm.pattern, arm.guard.as_mut(), &mut arm.body);
                }
            }
            StmtKind::Break(_)
            | StmtKind::Continue(_)
            | StmtKind::Return(None)
            | StmtKind::Error => {}
        }
    }

    fn arm(&mut self, pattern: &mut Pattern, guard: Option<&mut Expr>, body: &mut ArmBody) {
        self.pattern(pattern);
        let mut names = Vec::new();
        pattern_names(pattern, &mut names);
        self.shadowed.push(names);
        if let Some(guard) = guard {
            self.expr(guard);
        }
        match body {
            ArmBody::Block(block) => self.block(block),
            ArmBody::Expr(expression) => self.expr(expression),
        }
        self.shadowed.pop();
    }

    fn expr(&mut self, expression: &mut Expr) {
        self.span(&mut expression.span);
        match &mut expression.kind {
            ExprKind::Name(name) => {
                if self.is_shadowed(name) {
                    return;
                }
                if let Some(value) = self.values.get(name) {
                    match self.literal(value, expression.span) {
                        Some(replacement) => *expression = replacement,
                        None => self.errors.push((
                            expression.span,
                            format!("`{name}` is not a value a generated body can capture"),
                        )),
                    }
                }
            }
            ExprKind::Interpolation(parts) => {
                for part in parts {
                    if let InterpolationPart::Expr(expression) = part {
                        self.expr(expression);
                    }
                }
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Try(operand)
            | ExprKind::Await(operand)
            | ExprKind::AddressOf { operand, .. } => self.expr(operand),
            ExprKind::Cast { value, ty } | ExprKind::TypeTest { value, ty } => {
                self.expr(value);
                self.ty(ty);
            }
            ExprKind::Binary {
                op_span,
                left,
                right,
                ..
            } => {
                self.span(op_span);
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Range { start, end, .. } => {
                if let Some(start) = start {
                    self.expr(start);
                }
                if let Some(end) = end {
                    self.expr(end);
                }
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
                ..
            } => {
                self.expr(callee);
                for ty in type_args {
                    self.ty(ty);
                }
                for argument in args {
                    self.argument(argument);
                }
            }
            ExprKind::Field { receiver, .. } => self.expr(receiver),
            ExprKind::Index {
                receiver, index, ..
            } => {
                self.expr(receiver);
                self.expr(index);
            }
            ExprKind::Tuple(values) | ExprKind::List(values) | ExprKind::Set(values) => {
                for value in values {
                    self.expr(value);
                }
            }
            ExprKind::Record { fields, .. } => {
                for field in fields {
                    self.span(&mut field.span);
                    self.expr(&mut field.value);
                }
            }
            ExprKind::Map(entries) => {
                for entry in entries {
                    self.span(&mut entry.span);
                    if let MapKey::Computed(key) = &mut entry.key {
                        self.expr(key);
                    }
                    self.expr(&mut entry.value);
                }
            }
            ExprKind::Function {
                params,
                result,
                body,
                ..
            } => {
                let mut names = Vec::new();
                for param in params.iter() {
                    binding_names(&param.binding, &mut names);
                }
                self.shadowed.push(names);
                self.function(params, result.as_mut(), body);
                self.shadowed.pop();
            }
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                for arm in arms {
                    self.span(&mut arm.span);
                    self.arm(&mut arm.pattern, arm.guard.as_mut(), &mut arm.body);
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
            | ExprKind::Error => {}
        }
    }

    fn argument(&mut self, argument: &mut Argument) {
        self.span(&mut argument.span);
        self.expr(&mut argument.value);
    }

    fn ty(&mut self, ty: &mut Type) {
        self.span(&mut ty.span);
        match &mut ty.kind {
            TypeKind::Path { args, .. } => {
                for arg in args {
                    self.ty(arg);
                }
            }
            TypeKind::Optional(inner) | TypeKind::Pointer { target: inner, .. } => {
                self.ty(inner);
            }
            TypeKind::Union(types) | TypeKind::Intersection(types) | TypeKind::Tuple(types) => {
                for ty in types {
                    self.ty(ty);
                }
            }
            TypeKind::Function { params, result, .. } => {
                for param in params {
                    self.ty(param);
                }
                self.ty(result);
            }
            TypeKind::Array { element, length } => {
                self.ty(element);
                self.expr(length);
            }
            TypeKind::Record(fields) => {
                for field in fields {
                    self.span(&mut field.span);
                    self.ty(&mut field.ty);
                }
            }
            TypeKind::Error => {}
        }
    }

    fn pattern(&mut self, pattern: &mut Pattern) {
        self.span(&mut pattern.span);
        match &mut pattern.kind {
            PatternKind::Literal(expression) => self.expr(expression),
            PatternKind::Range { start, end, .. } => {
                self.expr(start);
                self.expr(end);
            }
            PatternKind::Path { payload, .. } => match payload {
                Some(Payload::Tuple(patterns)) => {
                    for pattern in patterns {
                        self.pattern(pattern);
                    }
                }
                Some(Payload::Record { fields, .. }) => {
                    for field in fields {
                        self.span(&mut field.span);
                        if let Some(pattern) = &mut field.pattern {
                            self.pattern(pattern);
                        }
                    }
                }
                None => {}
            },
            PatternKind::Sequence { before, after, .. } => {
                for pattern in before.iter_mut().chain(after) {
                    self.pattern(pattern);
                }
            }
            PatternKind::Tuple(patterns) | PatternKind::Or(patterns) => {
                for pattern in patterns {
                    self.pattern(pattern);
                }
            }
            PatternKind::Typed { inner, ty } => {
                self.pattern(inner);
                self.ty(ty);
            }
            PatternKind::Wildcard | PatternKind::Binding(_) | PatternKind::Error => {}
        }
    }

    fn binding(&mut self, binding: &mut Binding) {
        match binding {
            Binding::Record(fields) => {
                for field in fields {
                    self.span(&mut field.span);
                }
            }
            Binding::Tuple(bindings) => {
                for binding in bindings {
                    self.binding(binding);
                }
            }
            Binding::Name(_) | Binding::Error => {}
        }
    }

    fn declare(&mut self, binding: &mut Binding) {
        self.binding(binding);
        let scope = self.shadowed.last_mut().expect("a body is open");
        binding_names(binding, scope);
    }

    fn is_shadowed(&self, name: &str) -> bool {
        self.shadowed
            .iter()
            .any(|scope| scope.iter().any(|bound| bound == name))
    }

    fn literal(&mut self, value: &Value, span: Span) -> Option<Expr> {
        let kind = match value {
            Value::Nil => ExprKind::Nil,
            Value::Bool(value) => ExprKind::Bool(*value),
            Value::Integer(value) => ExprKind::Integer(*value),
            Value::String(value) => ExprKind::String(value.clone()),
            Value::List(values) => {
                let mut elements = Vec::with_capacity(values.len());
                for value in values {
                    let span = self.fresh();
                    elements.push(self.literal(value, span)?);
                }
                ExprKind::List(elements)
            }
            Value::Record(fields) => {
                let mut inits = Vec::with_capacity(fields.len());
                for (name, value) in fields {
                    let span = self.fresh();
                    inits.push(FieldInit {
                        name: name.clone(),
                        value: self.literal(value, span)?,
                        span,
                    });
                }
                ExprKind::Record {
                    path: Vec::new(),
                    fields: inits,
                }
            }
            Value::Target | Value::Function(_) | Value::Map(_) => return None,
        };
        Some(Expr::new(kind, span))
    }
}

fn binding_names(binding: &Binding, names: &mut Vec<String>) {
    match binding {
        Binding::Name(name) => names.push(name.clone()),
        Binding::Record(fields) => {
            for field in fields {
                names.push(
                    field
                        .bound_as
                        .clone()
                        .unwrap_or_else(|| field.field.clone()),
                );
            }
        }
        Binding::Tuple(bindings) => {
            for binding in bindings {
                binding_names(binding, names);
            }
        }
        Binding::Error => {}
    }
}

fn pattern_names(pattern: &Pattern, names: &mut Vec<String>) {
    match &pattern.kind {
        PatternKind::Binding(name) => names.push(name.clone()),
        PatternKind::Path { payload, .. } => match payload {
            Some(Payload::Tuple(patterns)) => {
                for pattern in patterns {
                    pattern_names(pattern, names);
                }
            }
            Some(Payload::Record { fields, .. }) => {
                for field in fields {
                    match &field.pattern {
                        Some(pattern) => pattern_names(pattern, names),
                        None => names.push(
                            field
                                .bound_as
                                .clone()
                                .unwrap_or_else(|| field.field.clone()),
                        ),
                    }
                }
            }
            None => {}
        },
        PatternKind::Sequence {
            before,
            rest,
            after,
        } => {
            for pattern in before.iter().chain(after) {
                pattern_names(pattern, names);
            }
            if let Some(Some(name)) = rest {
                names.push(name.clone());
            }
        }
        PatternKind::Tuple(patterns) | PatternKind::Or(patterns) => {
            for pattern in patterns {
                pattern_names(pattern, names);
            }
        }
        PatternKind::Typed { inner, .. } => pattern_names(inner, names),
        PatternKind::Wildcard
        | PatternKind::Literal(_)
        | PatternKind::Range { .. }
        | PatternKind::Error => {}
    }
}
