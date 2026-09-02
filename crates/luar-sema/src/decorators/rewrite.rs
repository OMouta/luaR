//! Rewriting a generated body: captured values are spliced in, staged
//! control flow is written out, and every span moves to a file of its own
//! (LR23.1).

use std::collections::BTreeMap;

use luar_ast::{
    Argument, ArmBody, Binding, Block, Branch, Expr, ExprKind, FieldInit, FunctionBody,
    InterpolationPart, MapKey, Param, Pattern, PatternKind, Payload, Stmt, StmtKind, Type,
    TypeKind, UnaryOp,
};
use luar_diagnostics::{FileId, SourceMap, Span};

use super::Value;

pub(super) struct Rewrite<'a> {
    sources: &'a mut SourceMap,
    /// The decorator's file, which every copy is of.
    base: FileId,
    pub(super) file: FileId,
    /// The next offset past the file's text, for a node with no source of
    /// its own.
    next: u32,
    values: BTreeMap<String, Value>,
    shadowed: Vec<Vec<String>>,
    pub(super) errors: Vec<(Span, String)>,
}

impl<'a> Rewrite<'a> {
    pub(super) fn new(
        sources: &'a mut SourceMap,
        base: FileId,
        values: BTreeMap<String, Value>,
        params: &[Param],
    ) -> Self {
        let mut names = Vec::new();
        for param in params {
            binding_names(&param.binding, &mut names);
        }
        let file = sources.copy(base);
        let next = text_len(sources, base);
        Self {
            sources,
            base,
            file,
            next,
            values,
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
        let statements = std::mem::take(&mut block.stmts);
        let mut written = Vec::with_capacity(statements.len());
        for statement in statements {
            self.stmt(statement, &mut written);
        }
        block.stmts = written;
        self.shadowed.pop();
    }

    /// Writes `statement` out into `written`: as itself, or as what a staged
    /// `for` or `if` stands for.
    fn stmt(&mut self, mut statement: Stmt, written: &mut Vec<Stmt>) {
        self.span(&mut statement.span);
        let kind = std::mem::replace(&mut statement.kind, StmtKind::Error);
        match kind {
            StmtKind::For {
                bindings,
                iterable,
                body,
                label,
            } => {
                if let [Binding::Name(name)] = bindings.as_slice()
                    && let Some(Value::List(values)) = self.fold(&iterable)
                {
                    self.unroll(name, values, &body, written);
                    return;
                }
                statement.kind = StmtKind::For {
                    bindings,
                    iterable,
                    body,
                    label,
                };
            }
            StmtKind::If {
                branches,
                otherwise,
            } => {
                let Some((branches, otherwise)) = self.select(branches, otherwise, written) else {
                    return;
                };
                statement.kind = StmtKind::If {
                    branches,
                    otherwise,
                };
            }
            kind => statement.kind = kind,
        }
        self.runtime(&mut statement);
        written.push(statement);
    }

    /// LR23.1: a `for` over a captured list is written out once per element.
    fn unroll(&mut self, name: &str, values: Vec<Value>, body: &Block, written: &mut Vec<Stmt>) {
        let previous = self.values.remove(name);
        let (file, next) = (self.file, self.next);
        for value in values {
            self.values.insert(name.to_owned(), value);
            self.file = self.sources.copy(self.base);
            self.next = text_len(self.sources, self.base);
            for statement in body.stmts.clone() {
                self.stmt(statement, written);
            }
        }
        self.file = file;
        self.next = next;
        match previous {
            Some(previous) => self.values.insert(name.to_owned(), previous),
            None => self.values.remove(name),
        };
    }

    /// LR23.1: an `if` on captured conditions keeps the branch it selects.
    /// Gives back what is left to decide at runtime, if anything is.
    fn select(
        &mut self,
        branches: Vec<Branch>,
        otherwise: Option<Block>,
        written: &mut Vec<Stmt>,
    ) -> Option<(Vec<Branch>, Option<Block>)> {
        let mut kept = Vec::new();
        for branch in branches {
            match self.fold(&branch.condition) {
                Some(Value::Bool(true)) => {
                    if kept.is_empty() {
                        for statement in branch.body.stmts {
                            self.stmt(statement, written);
                        }
                        return None;
                    }
                    return Some((kept, Some(branch.body)));
                }
                Some(Value::Bool(false)) => {}
                _ => kept.push(branch),
            }
        }
        if kept.is_empty() {
            if let Some(otherwise) = otherwise {
                for statement in otherwise.stmts {
                    self.stmt(statement, written);
                }
            }
            return None;
        }
        Some((kept, otherwise))
    }

    fn runtime(&mut self, statement: &mut Stmt) {
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
                let statements = std::mem::take(&mut body.stmts);
                let mut written = Vec::with_capacity(statements.len());
                for statement in statements {
                    self.stmt(statement, &mut written);
                }
                body.stmts = written;
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

    /// LR23.1: the value of an expression over captured values alone.
    fn fold(&self, expression: &Expr) -> Option<Value> {
        match &expression.kind {
            ExprKind::Nil => Some(Value::Nil),
            ExprKind::Bool(value) => Some(Value::Bool(*value)),
            ExprKind::Integer(value) => Some(Value::Integer(*value)),
            ExprKind::String(value) => Some(Value::String(value.clone())),
            ExprKind::Name(name) if !self.is_shadowed(name) => self.values.get(name).cloned(),
            ExprKind::Field {
                receiver,
                name,
                optional: false,
            } => match self.fold(receiver)? {
                Value::Record(record) => record.get(name).cloned(),
                _ => None,
            },
            ExprKind::Unary {
                op: UnaryOp::Not,
                operand,
            } => match self.fold(operand)? {
                Value::Bool(value) => Some(Value::Bool(!value)),
                _ => None,
            },
            ExprKind::Binary {
                op, left, right, ..
            } => super::apply(*op, self.fold(left)?, self.fold(right)?),
            _ => None,
        }
    }

    fn expr(&mut self, expression: &mut Expr) {
        self.span(&mut expression.span);
        if matches!(
            expression.kind,
            ExprKind::Name(_)
                | ExprKind::Field { .. }
                | ExprKind::Unary { .. }
                | ExprKind::Binary { .. }
        ) && let Some(value) = self.fold(expression)
        {
            match self.literal(&value, expression.span) {
                Some(replacement) => {
                    *expression = replacement;
                    return;
                }
                None => {
                    if let ExprKind::Name(name) = &expression.kind {
                        self.errors.push((
                            expression.span,
                            format!("`{name}` is not a value a generated body can capture"),
                        ));
                        return;
                    }
                }
            }
        }
        if let Some(read) = self.field_read(expression) {
            *expression = read;
            return;
        }
        match &mut expression.kind {
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
            ExprKind::Name(_)
            | ExprKind::Nil
            | ExprKind::Bool(_)
            | ExprKind::Integer(_)
            | ExprKind::Float(_)
            | ExprKind::String(_)
            | ExprKind::ByteString(_)
            | ExprKind::Char(_)
            | ExprKind::Error => {}
        }
    }

    /// LR23.1: `field:get(value)` on a captured field reads that field.
    fn field_read(&mut self, expression: &Expr) -> Option<Expr> {
        let ExprKind::Call {
            callee,
            method: Some(method),
            args,
            ..
        } = &expression.kind
        else {
            return None;
        };
        if method != "get" {
            return None;
        }
        let Value::Record(field) = self.fold(callee)? else {
            return None;
        };
        let (Some(Value::String(name)), Some(_)) = (field.get("name"), field.get("typeName"))
        else {
            return None;
        };
        let [
            Argument {
                name: None, value, ..
            },
        ] = args.as_slice()
        else {
            return None;
        };
        let mut receiver = value.clone();
        self.expr(&mut receiver);
        Some(Expr::new(
            ExprKind::Field {
                receiver: Box::new(receiver),
                name: name.clone(),
                optional: false,
            },
            expression.span,
        ))
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

fn text_len(sources: &SourceMap, file: FileId) -> u32 {
    u32::try_from(sources.file(file).text().len()).expect("source offsets fit in u32")
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
