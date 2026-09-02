//! Package decorator expansion (LR23.1).

use std::collections::BTreeMap;

use luar_ast::{
    Argument, BinaryOp, Binding, Block, Decorator, DecoratorDecl, Expr, ExprKind, Function,
    FunctionBody, Item, Member, Param, StmtKind, Type, TypeKind, UnaryOp,
};
use luar_diagnostics::{Diagnostic, SourceMap, Span, codes};

use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin};

mod rewrite;

use rewrite::Rewrite;

#[derive(Clone)]
pub(super) enum Value {
    Target,
    Nil,
    Bool(bool),
    Integer(u64),
    String(String),
    List(Vec<Value>),
    Record(BTreeMap<String, Value>),
    Function {
        asynchronous: bool,
        params: Vec<Param>,
        result: Option<Type>,
        body: FunctionBody,
        span: Span,
    },
    Map(BTreeMap<String, Value>),
}

struct Target {
    name: String,
    kind: &'static str,
    fields: Vec<Value>,
    variants: Vec<Value>,
    attributes: Vec<Value>,
    span: Span,
}

enum Change {
    Method(Function),
    Attribute(Decorator),
    Implementation {
        interface: Type,
        methods: Vec<Function>,
    },
}

struct Evaluator<'a> {
    target: &'a Target,
    declaration: Span,
    application: Span,
    sources: &'a mut SourceMap,
    values: BTreeMap<String, Value>,
    changes: Vec<Change>,
    diagnostics: Vec<Diagnostic>,
}

pub fn expand(graph: &mut Graph, names: &Names, sources: &mut SourceMap) -> Vec<Diagnostic> {
    let modules: Vec<ModuleId> = graph.modules().map(|(id, _)| id).collect();
    let mut diagnostics = Vec::new();

    for module in modules {
        let items = graph.module(module).ast.items.clone();
        let mut expanded = Vec::with_capacity(items.len());
        for mut item in items {
            let changes = expand_item(&mut item, module, graph, names, sources, &mut diagnostics);
            expanded.push(item);
            expanded.extend(changes.into_iter().map(|change| match change {
                Change::Method(function) => Item::Function(function),
                Change::Attribute(_) | Change::Implementation { .. } => {
                    unreachable!("target changes are applied before methods are emitted")
                }
            }));
        }
        graph.module_mut(module).ast.items = expanded;
    }

    diagnostics
}

fn expand_item(
    item: &mut Item,
    module: ModuleId,
    graph: &Graph,
    names: &Names,
    sources: &mut SourceMap,
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<Change> {
    let Some(target) = target(item) else {
        return Vec::new();
    };

    let mut decorators = take_decorators(item);
    let changes = expand_decorators(
        &mut decorators,
        &target,
        module,
        graph,
        names,
        sources,
        diagnostics,
    );
    put_decorators(item, decorators);
    apply_changes(item, changes, diagnostics)
}

fn expand_decorators(
    decorators: &mut Vec<Decorator>,
    target: &Target,
    module: ModuleId,
    graph: &Graph,
    names: &Names,
    sources: &mut SourceMap,
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<Change> {
    let mut changes = Vec::new();
    let mut retained = Vec::new();

    for mut decorator in std::mem::take(decorators) {
        if decorator.name == "derive" {
            let mut arguments = Vec::new();
            for argument in decorator.args {
                let ExprKind::Name(name) = &argument.value.kind else {
                    arguments.push(argument);
                    continue;
                };
                if matches!(name.as_str(), "Eq" | "Hash" | "Display") {
                    arguments.push(argument);
                    continue;
                }
                let Some(declaration) = declaration(module, name, graph, names) else {
                    arguments.push(argument);
                    continue;
                };
                changes.extend(run(
                    &declaration,
                    &[],
                    target,
                    argument.span,
                    sources,
                    diagnostics,
                ));
            }
            decorator.args = arguments;
            if !decorator.args.is_empty() {
                retained.push(decorator);
            }
        } else if builtin(&decorator.name) {
            retained.push(decorator);
        } else if let Some(declaration) = declaration(module, &decorator.name, graph, names) {
            changes.extend(run(
                &declaration,
                &decorator.args,
                target,
                decorator.span,
                sources,
                diagnostics,
            ));
        } else {
            retained.push(decorator);
        }
    }

    *decorators = retained;
    changes
}

fn declaration(
    module: ModuleId,
    name: &str,
    graph: &Graph,
    names: &Names,
) -> Option<DecoratorDecl> {
    let binding = names.scope(module).get(name)?;
    let (origin, name) = match &binding.origin {
        Origin::Declared { .. } => (module, name),
        Origin::Imported { module, name } => (*module, name.as_str()),
        Origin::Binding { .. } | Origin::Namespace(_) => return None,
    };
    graph
        .module(origin)
        .ast
        .items
        .iter()
        .find_map(|item| match item {
            Item::DecoratorDecl(declaration) if declaration.name == name => {
                Some(declaration.clone())
            }
            _ => None,
        })
}

fn run(
    declaration: &DecoratorDecl,
    arguments: &[Argument],
    target: &Target,
    application: Span,
    sources: &mut SourceMap,
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<Change> {
    let mut evaluator = Evaluator {
        target,
        declaration: declaration.span,
        application,
        sources,
        values: BTreeMap::new(),
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
    evaluator.bind_arguments(&declaration.params[1..], arguments);
    evaluator.block(&declaration.body);
    diagnostics.extend(evaluator.diagnostics);
    evaluator.changes
}

impl Evaluator<'_> {
    fn bind_arguments(&mut self, params: &[Param], arguments: &[Argument]) {
        let mut positional = arguments.iter().filter(|argument| argument.name.is_none());
        for param in params {
            let Binding::Name(name) = &param.binding else {
                self.error(param.span, "a decorator parameter must bind one name");
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
                self.values.insert(name.clone(), value);
            } else {
                self.error(
                    param.span,
                    format!("decorator argument `{name}` is missing"),
                );
            }
        }
    }

    fn block(&mut self, block: &Block) {
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
                    if let Some(block) = selected.or(otherwise.as_ref()) {
                        self.block(block);
                    }
                }
                StmtKind::For {
                    bindings,
                    iterable,
                    body,
                    ..
                } => self.for_loop(bindings, iterable, body, statement.span),
                StmtKind::Expr(expression) => {
                    self.expression(expression);
                }
                StmtKind::Return(_) => break,
                _ => self.error(
                    statement.span,
                    "statement cannot run while expanding a decorator",
                ),
            }
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
            } => self.binary(*op, left, right, expression.span),
            ExprKind::Function {
                asynchronous,
                params,
                result,
                body,
            } => Some(Value::Function {
                asynchronous: *asynchronous,
                params: params.clone(),
                result: result.clone(),
                body: (**body).clone(),
                span: expression.span,
            }),
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

    fn for_loop(&mut self, bindings: &[Binding], iterable: &Expr, body: &Block, span: Span) {
        let [Binding::Name(name)] = bindings else {
            self.error(span, "a metadata loop binds one name");
            return;
        };
        let Some(Value::List(values)) = self.expression(iterable) else {
            self.error(span, "a metadata loop iterates a frozen list");
            return;
        };
        let previous = self.values.remove(name);
        for value in values {
            self.values.insert(name.clone(), value);
            self.block(body);
        }
        if let Some(previous) = previous {
            self.values.insert(name.clone(), previous);
        } else {
            self.values.remove(name);
        }
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

    fn binary(&mut self, op: BinaryOp, left: &Expr, right: &Expr, span: Span) -> Option<Value> {
        let left = self.expression(left)?;
        let right = self.expression(right)?;
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
        if !self.is_target(callee) {
            self.error(
                span,
                "only declaration metadata operations run during expansion",
            );
            return None;
        }
        match method {
            Some("addMethod") => self.add_method(arguments, span),
            Some("addImplementation") => self.add_implementation(arguments, span),
            Some("addAttribute") => self.add_attribute(arguments, span),
            Some("report") => self.report(arguments, span),
            Some(name) => self.error(span, format!("unknown declaration operation `{name}`")),
            None => self.error(span, "declaration metadata is not callable"),
        }
        Some(Value::Nil)
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
        let Some(Value::Function {
            asynchronous,
            mut params,
            mut result,
            mut body,
            span,
        }) = self.argument(arguments, 1)
        else {
            self.error(span, "addMethod expects a function body");
            return;
        };
        let span = self.rewrite(span, &mut params, result.as_mut(), &mut body);
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
            let Value::Function {
                asynchronous,
                mut params,
                mut result,
                mut body,
                span,
            } = value
            else {
                self.error(span, "an implementation method must be a function");
                continue;
            };
            let span = self.rewrite(span, &mut params, result.as_mut(), &mut body);
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
        if !builtin(&name) {
            self.error(span, format!("`{name}` is not a built-in attribute"));
            return;
        }
        let mut args = Vec::new();
        for argument in &arguments[1..] {
            let Some(value) = self.expression(&argument.value) else {
                continue;
            };
            let Some(value) = literal(value, argument.span) else {
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
        span: Span,
        params: &mut [Param],
        result: Option<&mut Type>,
        body: &mut FunctionBody,
    ) -> Span {
        let text_len = self.sources.file(self.declaration.file).text().len();
        let file = self.sources.copy(self.declaration.file);
        let mut rewrite = Rewrite::new(
            &self.values,
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

fn literal(value: Value, span: Span) -> Option<Expr> {
    let kind = match value {
        Value::Nil => ExprKind::Nil,
        Value::Bool(value) => ExprKind::Bool(value),
        Value::Integer(value) => ExprKind::Integer(value),
        Value::String(value) => ExprKind::String(value),
        Value::Target
        | Value::List(_)
        | Value::Record(_)
        | Value::Function { .. }
        | Value::Map(_) => return None,
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

fn apply_changes(
    item: &mut Item,
    changes: Vec<Change>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<Change> {
    let mut methods = Vec::new();
    for change in changes {
        match change {
            Change::Method(function) => methods.push(Change::Method(function)),
            Change::Attribute(decorator) => decorators_mut(item).push(decorator),
            Change::Implementation {
                interface,
                methods: added,
            } => {
                if let Item::Struct(structure) = item {
                    structure.implements.push(interface);
                    methods.extend(added.into_iter().map(Change::Method));
                } else {
                    diagnostics.push(Diagnostic::error(
                        codes::DECORATOR_EXPANSION,
                        item_span(item),
                        "only a struct can gain an interface implementation",
                    ));
                }
            }
        }
    }
    methods
}

fn target(item: &Item) -> Option<Target> {
    let (name, kind, decorators, span) = match item {
        Item::Function(function) => (
            function.name.join("."),
            "function",
            &function.decorators,
            function.span,
        ),
        Item::Struct(structure) => (
            structure.name.clone(),
            "struct",
            &structure.decorators,
            structure.span,
        ),
        Item::Enum(enumeration) => (
            enumeration.name.clone(),
            "enum",
            &enumeration.decorators,
            enumeration.span,
        ),
        Item::Interface(interface) => (
            interface.name.clone(),
            "interface",
            &interface.decorators,
            interface.span,
        ),
        Item::Extend(extend) => (
            extend.name.clone(),
            "extension",
            &extend.decorators,
            extend.span,
        ),
        Item::TypeAlias(alias) => (alias.name.clone(), "alias", &alias.decorators, alias.span),
        Item::Import(_) | Item::DecoratorDecl(_) | Item::Stmt(_) => return None,
    };

    let fields = match item {
        Item::Struct(structure) => structure
            .members
            .iter()
            .filter_map(|member| match member {
                Member::Field(field) => Some(metadata([
                    ("name", field.name.clone()),
                    ("typeName", type_name(&field.ty)),
                ])),
                Member::Function { .. } | Member::Property(_) => None,
            })
            .collect(),
        _ => Vec::new(),
    };
    let variants = match item {
        Item::Enum(enumeration) => enumeration
            .variants
            .iter()
            .map(|variant| metadata([("name", variant.name.clone())]))
            .collect(),
        _ => Vec::new(),
    };
    let attributes = decorators
        .iter()
        .map(|decorator| Value::String(decorator.name.clone()))
        .collect();

    Some(Target {
        name,
        kind,
        fields,
        variants,
        attributes,
        span,
    })
}

fn metadata<const N: usize>(fields: [(&str, String); N]) -> Value {
    Value::Record(
        fields
            .into_iter()
            .map(|(name, value)| (name.to_owned(), Value::String(value)))
            .collect(),
    )
}

fn type_name(ty: &Type) -> String {
    match &ty.kind {
        TypeKind::Path { segments, args } => {
            let mut name = segments.join(".");
            if !args.is_empty() {
                name.push('<');
                name.push_str(&args.iter().map(type_name).collect::<Vec<_>>().join(", "));
                name.push('>');
            }
            name
        }
        TypeKind::Optional(inner) => format!("{}?", type_name(inner)),
        TypeKind::Union(types) => types.iter().map(type_name).collect::<Vec<_>>().join(" | "),
        TypeKind::Intersection(types) => {
            types.iter().map(type_name).collect::<Vec<_>>().join(" & ")
        }
        TypeKind::Tuple(types) => format!(
            "({})",
            types.iter().map(type_name).collect::<Vec<_>>().join(", ")
        ),
        TypeKind::Function {
            asynchronous,
            params,
            result,
        } => format!(
            "{}({}) -> {}",
            if *asynchronous { "async " } else { "" },
            params.iter().map(type_name).collect::<Vec<_>>().join(", "),
            type_name(result)
        ),
        TypeKind::Array { element, length } => {
            format!("[{}; {}]", type_name(element), const_name(length))
        }
        TypeKind::Pointer { mutable, target } => format!(
            "*{} {}",
            if *mutable { "mut" } else { "const" },
            type_name(target)
        ),
        TypeKind::Record(fields) => format!(
            "{{ {} }}",
            fields
                .iter()
                .map(|field| format!("{}: {}", field.name, type_name(&field.ty)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        TypeKind::Error => "<error>".to_owned(),
    }
}

fn const_name(expression: &Expr) -> String {
    match &expression.kind {
        ExprKind::Integer(value) => value.to_string(),
        ExprKind::Name(name) => name.clone(),
        _ => "_".to_owned(),
    }
}

fn take_decorators(item: &mut Item) -> Vec<Decorator> {
    std::mem::take(decorators_mut(item))
}

fn put_decorators(item: &mut Item, decorators: Vec<Decorator>) {
    *decorators_mut(item) = decorators;
}

fn decorators_mut(item: &mut Item) -> &mut Vec<Decorator> {
    match item {
        Item::Function(function) => &mut function.decorators,
        Item::Struct(structure) => &mut structure.decorators,
        Item::Enum(enumeration) => &mut enumeration.decorators,
        Item::Interface(interface) => &mut interface.decorators,
        Item::Extend(extend) => &mut extend.decorators,
        Item::TypeAlias(alias) => &mut alias.decorators,
        Item::Import(_) | Item::DecoratorDecl(_) | Item::Stmt(_) => {
            unreachable!("only declarations have decorators")
        }
    }
}

fn item_span(item: &Item) -> Span {
    match item {
        Item::Import(import) => import.span,
        Item::DecoratorDecl(decorator) => decorator.span,
        Item::Function(function) => function.span,
        Item::Struct(structure) => structure.span,
        Item::Enum(enumeration) => enumeration.span,
        Item::Interface(interface) => interface.span,
        Item::Extend(extend) => extend.span,
        Item::TypeAlias(alias) => alias.span,
        Item::Stmt(statement) => statement.span,
    }
}

fn builtin(name: &str) -> bool {
    matches!(
        name,
        "inline"
            | "noinline"
            | "deprecated"
            | "cold"
            | "repr"
            | "test"
            | "finalizer"
            | "intrinsic"
            | "extern"
            | "reflect"
    )
}
