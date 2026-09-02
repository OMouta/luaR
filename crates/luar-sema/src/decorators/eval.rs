//! The compile-time evaluator a decorator body runs in (LR23.1).

use std::collections::BTreeMap;

use luar_ast::{
    Argument, BinaryOp, Binding, Block, Decorator, DecoratorDecl, Expr, ExprKind, Function,
    FunctionBody, Item, Param, StmtKind, Type, TypeKind, UnaryOp,
};
use luar_diagnostics::{Diagnostic, SourceMap, Span, codes};

use super::rewrite::Rewrite;
use super::{Change, FunctionValue, Program, Target, Value};
use crate::modules::ModuleId;

/// Helper calls nested deeper than this are runaway recursion.
const DEPTH_LIMIT: u32 = 64;

pub(super) struct Application<'a> {
    pub declaration: &'a DecoratorDecl,
    /// The module declaring the decorator, which its helper calls resolve in.
    pub module: ModuleId,
    pub arguments: &'a [Argument],
    pub span: Span,
}

pub(super) struct Evaluator<'a> {
    target: &'a Target,
    program: Program<'a>,
    module: ModuleId,
    declaration: Span,
    application: Span,
    sources: &'a mut SourceMap,
    values: BTreeMap<String, Value>,
    depth: u32,
    changes: Vec<Change>,
    diagnostics: Vec<Diagnostic>,
}

enum Flow {
    Next,
    Return(Option<Value>),
}

impl<'a> Evaluator<'a> {
    pub(super) fn run(
        target: &'a Target,
        program: Program<'a>,
        sources: &'a mut SourceMap,
        application: Application<'_>,
    ) -> (Vec<Change>, Vec<Diagnostic>) {
        let declaration = application.declaration;
        let mut evaluator = Evaluator {
            target,
            program,
            module: application.module,
            declaration: declaration.span,
            application: application.span,
            sources,
            values: BTreeMap::new(),
            depth: 0,
            changes: Vec::new(),
            diagnostics: Vec::new(),
        };

        if let Some(Param {
            binding: Binding::Name(name),
            ..
        }) = declaration.params.first()
        {
            evaluator.values.insert(name.clone(), Value::Target);
        }
        let params = declaration.params.get(1..).unwrap_or(&[]);
        let arguments = evaluator.arguments(params, application.arguments);
        evaluator.values.extend(arguments);
        evaluator.block(&declaration.body);
        (evaluator.changes, evaluator.diagnostics)
    }

    /// The values `params` take from `arguments`, evaluated where the call
    /// is written.
    fn arguments(&mut self, params: &[Param], arguments: &[Argument]) -> BTreeMap<String, Value> {
        let mut values = BTreeMap::new();
        let mut positional = arguments.iter().filter(|argument| argument.name.is_none());
        for param in params {
            let Binding::Name(name) = &param.binding else {
                self.error(param.span, "a compile-time parameter must bind one name");
                continue;
            };
            let argument = arguments
                .iter()
                .find(|argument| argument.name.as_deref() == Some(name))
                .or_else(|| positional.next());
            let expression = argument
                .map(|argument| &argument.value)
                .or(param.default.as_ref());
            if let Some(expression) = expression
                && let Some(value) = self.expression(expression)
            {
                values.insert(name.clone(), value);
            } else {
                self.error(param.span, format!("argument `{name}` is missing"));
            }
        }
        values
    }

    fn block(&mut self, block: &Block) -> Flow {
        for statement in &block.stmts {
            match &statement.kind {
                StmtKind::Local { binding, value, .. } => {
                    if let (Binding::Name(name), Some(value)) = (binding, value)
                        && let Some(value) = self.expression(value)
                    {
                        self.values.insert(name.clone(), value);
                    }
                }
                StmtKind::Const { binding, value, .. } => {
                    if let Binding::Name(name) = binding
                        && let Some(value) = self.expression(value)
                    {
                        self.values.insert(name.clone(), value);
                    }
                }
                StmtKind::Assign { target, op, value } => {
                    self.assign(target, *op, value, statement.span);
                }
                StmtKind::If {
                    branches,
                    otherwise,
                } => {
                    let mut selected = None;
                    for branch in branches {
                        if matches!(self.expression(&branch.condition), Some(Value::Bool(true))) {
                            selected = Some(&branch.body);
                            break;
                        }
                    }
                    if let Some(block) = selected.or(otherwise.as_ref())
                        && let Flow::Return(value) = self.block(block)
                    {
                        return Flow::Return(value);
                    }
                }
                StmtKind::For {
                    bindings,
                    iterable,
                    body,
                    ..
                } => {
                    if let Flow::Return(value) =
                        self.for_loop(bindings, iterable, body, statement.span)
                    {
                        return Flow::Return(value);
                    }
                }
                StmtKind::Expr(expression) => {
                    self.expression(expression);
                }
                StmtKind::Return(value) => {
                    return Flow::Return(value.as_ref().and_then(|value| self.expression(value)));
                }
                _ => self.error(
                    statement.span,
                    "statement cannot run while expanding a decorator",
                ),
            }
        }
        Flow::Next
    }

    fn assign(&mut self, target: &Expr, op: Option<BinaryOp>, value: &Expr, span: Span) {
        let ExprKind::Name(name) = &target.kind else {
            self.error(
                span,
                "only a local can be assigned while expanding a decorator",
            );
            return;
        };
        let Some(current) = self.values.get(name).cloned() else {
            self.error(target.span, format!("`{name}` is not a compile-time value"));
            return;
        };
        let Some(value) = self.expression(value) else {
            return;
        };
        let value = match op {
            Some(op) => self.apply(op, current, value, span),
            None => Some(value),
        };
        if let Some(value) = value {
            self.values.insert(name.clone(), value);
        }
    }

    fn expression(&mut self, expression: &Expr) -> Option<Value> {
        match &expression.kind {
            ExprKind::Nil => Some(Value::Nil),
            ExprKind::Bool(value) => Some(Value::Bool(*value)),
            ExprKind::Integer(value) => Some(Value::Integer(*value)),
            ExprKind::String(value) => Some(Value::String(value.clone())),
            ExprKind::List(values) => Some(Value::List(
                values
                    .iter()
                    .filter_map(|value| self.expression(value))
                    .collect(),
            )),
            ExprKind::Record { path, fields } if path.is_empty() => {
                let mut record = BTreeMap::new();
                for field in fields {
                    if let Some(value) = self.expression(&field.value) {
                        record.insert(field.name.clone(), value);
                    }
                }
                Some(Value::Record(record))
            }
            ExprKind::Name(name) => self.values.get(name).cloned().or_else(|| {
                self.error(
                    expression.span,
                    format!("`{name}` is not a compile-time value"),
                );
                None
            }),
            ExprKind::Field { receiver, name, .. } => self.field(receiver, name, expression.span),
            ExprKind::Unary { op, operand } => self.unary(*op, operand, expression.span),
            ExprKind::Binary {
                op, left, right, ..
            } => {
                let left = self.expression(left)?;
                let right = self.expression(right)?;
                self.apply(*op, left, right, expression.span)
            }
            ExprKind::Function {
                asynchronous,
                params,
                result,
                body,
            } => Some(Value::Function(Box::new(FunctionValue {
                asynchronous: *asynchronous,
                params: params.clone(),
                result: result.clone(),
                body: (**body).clone(),
                span: expression.span,
                captures: self.values.clone(),
            }))),
            ExprKind::Map(entries) => {
                let mut map = BTreeMap::new();
                for entry in entries {
                    let luar_ast::MapKey::Name(name) = &entry.key else {
                        self.error(entry.span, "a decorator method map uses name keys");
                        continue;
                    };
                    if let Some(value) = self.expression(&entry.value) {
                        map.insert(name.clone(), value);
                    }
                }
                Some(Value::Map(map))
            }
            ExprKind::Call {
                callee,
                method,
                args,
                ..
            } => self.call(callee, method.as_deref(), args, expression.span),
            _ => {
                self.error(
                    expression.span,
                    "expression cannot run while expanding a decorator",
                );
                None
            }
        }
    }

    fn field(&mut self, receiver: &Expr, name: &str, span: Span) -> Option<Value> {
        match self.expression(receiver)? {
            Value::Target => match name {
                "name" => Some(Value::String(self.target.name.clone())),
                "kind" => Some(Value::String(self.target.kind.to_owned())),
                "fields" => Some(Value::List(self.target.fields.clone())),
                "variants" => Some(Value::List(self.target.variants.clone())),
                "attributes" => Some(Value::List(self.target.attributes.clone())),
                _ => {
                    self.error(span, format!("unknown declaration metadata `{name}`"));
                    None
                }
            },
            Value::Record(record) => record.get(name).cloned().or_else(|| {
                self.error(span, format!("unknown metadata field `{name}`"));
                None
            }),
            _ => {
                self.error(span, "metadata field receiver is not a declaration value");
                None
            }
        }
    }

    fn for_loop(
        &mut self,
        bindings: &[Binding],
        iterable: &Expr,
        body: &Block,
        span: Span,
    ) -> Flow {
        let [Binding::Name(name)] = bindings else {
            self.error(span, "a metadata loop binds one name");
            return Flow::Next;
        };
        let Some(Value::List(values)) = self.expression(iterable) else {
            self.error(span, "a metadata loop iterates a frozen list");
            return Flow::Next;
        };
        let previous = self.values.remove(name);
        let mut flow = Flow::Next;
        for value in values {
            self.values.insert(name.clone(), value);
            if let Flow::Return(value) = self.block(body) {
                flow = Flow::Return(value);
                break;
            }
        }
        if let Some(previous) = previous {
            self.values.insert(name.clone(), previous);
        } else {
            self.values.remove(name);
        }
        flow
    }

    fn unary(&mut self, op: UnaryOp, operand: &Expr, span: Span) -> Option<Value> {
        match (op, self.expression(operand)?) {
            (UnaryOp::Not, Value::Bool(value)) => Some(Value::Bool(!value)),
            _ => {
                self.error(span, "invalid compile-time unary operation");
                None
            }
        }
    }

    fn apply(&mut self, op: BinaryOp, left: Value, right: Value, span: Span) -> Option<Value> {
        match (op, left, right) {
            (BinaryOp::Equal, Value::String(left), Value::String(right)) => {
                Some(Value::Bool(left == right))
            }
            (BinaryOp::NotEqual, Value::String(left), Value::String(right)) => {
                Some(Value::Bool(left != right))
            }
            (BinaryOp::Concat, Value::String(left), Value::String(right)) => {
                Some(Value::String(left + &right))
            }
            (BinaryOp::And, Value::Bool(left), Value::Bool(right)) => {
                Some(Value::Bool(left && right))
            }
            (BinaryOp::Or, Value::Bool(left), Value::Bool(right)) => {
                Some(Value::Bool(left || right))
            }
            (BinaryOp::Equal, Value::Integer(left), Value::Integer(right)) => {
                Some(Value::Bool(left == right))
            }
            (BinaryOp::NotEqual, Value::Integer(left), Value::Integer(right)) => {
                Some(Value::Bool(left != right))
            }
            _ => {
                self.error(span, "invalid compile-time binary operation");
                None
            }
        }
    }

    fn call(
        &mut self,
        callee: &Expr,
        method: Option<&str>,
        arguments: &[Argument],
        span: Span,
    ) -> Option<Value> {
        if self.is_target(callee) {
            match method {
                Some("addMethod") => self.add_method(arguments, span),
                Some("addImplementation") => self.add_implementation(arguments, span),
                Some("addAttribute") => self.add_attribute(arguments, span),
                Some("report") => self.report(arguments, span),
                Some(name) => self.error(span, format!("unknown declaration operation `{name}`")),
                None => self.error(span, "declaration metadata is not callable"),
            }
            return Some(Value::Nil);
        }
        if let (ExprKind::Name(name), None) = (&callee.kind, method)
            && !self.values.contains_key(name)
        {
            return self.helper(name, arguments, span);
        }
        self.error(
            span,
            "only declaration metadata operations and module functions run during expansion",
        );
        None
    }

    /// LR23.1: a call to a function of the decorator's module runs here.
    fn helper(&mut self, name: &str, arguments: &[Argument], span: Span) -> Option<Value> {
        let function = self
            .program
            .helpers
            .get(&(self.module, name.to_owned()))
            .or_else(|| module_function(self.program, self.module, name));
        let Some(body) = function.and_then(|function| function.body.as_ref()) else {
            self.error(
                span,
                format!("`{name}` is not a function of the decorator's module"),
            );
            return None;
        };
        if self.depth >= DEPTH_LIMIT {
            self.error(span, "decorator expansion recursed too deeply");
            return None;
        }
        let function = function.expect("a body belongs to a function");

        let values = self.arguments(&function.params, arguments);
        let outer = std::mem::replace(&mut self.values, values);
        self.depth += 1;
        let flow = self.block(body);
        self.depth -= 1;
        self.values = outer;
        Some(match flow {
            Flow::Return(value) => value.unwrap_or(Value::Nil),
            Flow::Next => Value::Nil,
        })
    }

    fn add_method(&mut self, arguments: &[Argument], span: Span) {
        if !matches!(self.target.kind, "struct" | "enum") {
            self.error(
                span,
                format!("cannot add a method to a {}", self.target.kind),
            );
            return;
        }
        let Some(Value::String(name)) = self.argument(arguments, 0) else {
            self.error(span, "addMethod expects a method name");
            return;
        };
        let Some(Value::Function(value)) = self.argument(arguments, 1) else {
            self.error(span, "addMethod expects a function body");
            return;
        };
        let FunctionValue {
            asynchronous,
            mut params,
            mut result,
            mut body,
            span,
            captures,
        } = *value;
        let span = self.rewrite(&captures, span, &mut params, result.as_mut(), &mut body);
        self.changes.push(Change::Method(function(
            &self.target.name,
            name,
            asynchronous,
            params,
            result,
            body,
            span,
        )));
    }

    fn add_implementation(&mut self, arguments: &[Argument], span: Span) {
        if self.target.kind != "struct" {
            self.error(
                span,
                format!("cannot add an implementation to a {}", self.target.kind),
            );
            return;
        }
        let Some(Value::String(interface)) = self.argument(arguments, 0) else {
            self.error(span, "addImplementation expects an interface name");
            return;
        };
        let Some(Value::Map(methods)) = self.argument(arguments, 1) else {
            self.error(span, "addImplementation expects a method map");
            return;
        };
        let mut functions = Vec::new();
        for (name, value) in methods {
            let Value::Function(value) = value else {
                self.error(span, "an implementation method must be a function");
                continue;
            };
            let FunctionValue {
                asynchronous,
                mut params,
                mut result,
                mut body,
                span,
                captures,
            } = *value;
            let span = self.rewrite(&captures, span, &mut params, result.as_mut(), &mut body);
            functions.push(function(
                &self.target.name,
                name,
                asynchronous,
                params,
                result,
                body,
                span,
            ));
        }
        self.changes.push(Change::Implementation {
            interface: Type::new(
                TypeKind::Path {
                    segments: vec![interface],
                    args: Vec::new(),
                },
                self.application,
            ),
            methods: functions,
        });
    }

    fn add_attribute(&mut self, arguments: &[Argument], span: Span) {
        let Some(Value::String(name)) = self.argument(arguments, 0) else {
            self.error(span, "addAttribute expects an attribute name");
            return;
        };
        if !super::builtin(&name) {
            self.error(span, format!("`{name}` is not a built-in attribute"));
            return;
        }
        let mut args = Vec::new();
        for argument in &arguments[1..] {
            let Some(value) = self.expression(&argument.value) else {
                continue;
            };
            let Some(value) = scalar(value, argument.span) else {
                self.error(
                    argument.span,
                    "an attribute argument must be a scalar value",
                );
                continue;
            };
            args.push(Argument {
                name: argument.name.clone(),
                value,
                span: argument.span,
            });
        }
        self.changes.push(Change::Attribute(Decorator {
            name,
            args,
            span: self.application,
        }));
    }

    fn report(&mut self, arguments: &[Argument], span: Span) {
        let Some(Value::String(message)) = self.argument(arguments, 0) else {
            self.error(span, "report expects a message");
            return;
        };
        self.error(self.application, message);
    }

    /// A generated body gets a copy of the decorator's file to itself, so
    /// its spans identify it and nothing else. Returns `span` moved there.
    fn rewrite(
        &mut self,
        captures: &BTreeMap<String, Value>,
        span: Span,
        params: &mut [Param],
        result: Option<&mut Type>,
        body: &mut FunctionBody,
    ) -> Span {
        let text_len = self.sources.file(self.declaration.file).text().len();
        let file = self.sources.copy(self.declaration.file);
        let mut rewrite = Rewrite::new(
            captures,
            file,
            u32::try_from(text_len).expect("source offsets fit in u32"),
            params,
        );
        rewrite.function(params, result, body);
        for (span, message) in rewrite.errors {
            self.error(span, message);
        }
        Span::new(file, span.start, span.end)
    }

    fn argument(&mut self, arguments: &[Argument], index: usize) -> Option<Value> {
        let expression = arguments.get(index).map(|argument| &argument.value)?;
        self.expression(expression)
    }

    fn is_target(&self, expression: &Expr) -> bool {
        matches!(&expression.kind, ExprKind::Name(name) if self.values.get(name).is_some_and(|value| matches!(value, Value::Target)))
    }

    fn error(&mut self, span: Span, message: impl Into<String>) {
        self.diagnostics.push(
            Diagnostic::error(codes::DECORATOR_EXPANSION, span, message)
                .label(self.declaration, "decorator declared here")
                .label(self.target.span, "attached declaration"),
        );
    }
}

/// The module-level function `name` of `module`, with its body.
fn module_function<'a>(program: Program<'a>, module: ModuleId, name: &str) -> Option<&'a Function> {
    program
        .graph
        .module(module)
        .ast
        .items
        .iter()
        .find_map(|item| match item {
            Item::Function(function)
                if function.name.as_slice() == [name] && function.body.is_some() =>
            {
                Some(function)
            }
            _ => None,
        })
}

fn scalar(value: Value, span: Span) -> Option<Expr> {
    let kind = match value {
        Value::Nil => ExprKind::Nil,
        Value::Bool(value) => ExprKind::Bool(value),
        Value::Integer(value) => ExprKind::Integer(value),
        Value::String(value) => ExprKind::String(value),
        Value::Target | Value::List(_) | Value::Record(_) | Value::Function(_) | Value::Map(_) => {
            return None;
        }
    };
    Some(Expr::new(kind, span))
}

fn function(
    owner: &str,
    name: String,
    asynchronous: bool,
    params: Vec<Param>,
    result: Option<Type>,
    body: FunctionBody,
    span: Span,
) -> Function {
    let body = match body {
        FunctionBody::Block(body) => body,
        FunctionBody::Expr(expression) => Block {
            stmts: vec![luar_ast::Stmt::new(
                StmtKind::Return(Some(expression)),
                span,
            )],
            span,
        },
    };
    Function {
        decorators: Vec::new(),
        exported: false,
        asynchronous,
        unsafe_: false,
        static_: false,
        name: vec![owner.to_owned(), name],
        type_params: Vec::new(),
        constraints: Vec::new(),
        params,
        result,
        body: Some(body),
        span,
    }
}
