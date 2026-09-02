//! Package decorator expansion (LR23.1).

use std::collections::BTreeMap;

use luar_ast::{
    BinaryOp, Decorator, DecoratorDecl, Expr, ExprKind, Function, FunctionBody, Item, Member,
    Param, Type, TypeKind,
};
use luar_diagnostics::{Diagnostic, SourceMap, Span, codes};

use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin};

mod eval;
mod rewrite;

use eval::{Application, Evaluator};

#[derive(Clone)]
enum Value {
    Target,
    Nil,
    Bool(bool),
    Integer(u64),
    String(String),
    List(Vec<Value>),
    Record(BTreeMap<String, Value>),
    Function(Box<FunctionValue>),
    Map(BTreeMap<String, Value>),
}

#[derive(Clone)]
struct FunctionValue {
    asynchronous: bool,
    params: Vec<Param>,
    result: Option<Type>,
    body: FunctionBody,
    span: Span,
    /// The compile-time values in scope where the function was written.
    captures: BTreeMap<String, Value>,
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

/// The binary operations a decorator body may use, over compile-time values.
fn apply(op: BinaryOp, left: Value, right: Value) -> Option<Value> {
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
        (BinaryOp::And, Value::Bool(left), Value::Bool(right)) => Some(Value::Bool(left && right)),
        (BinaryOp::Or, Value::Bool(left), Value::Bool(right)) => Some(Value::Bool(left || right)),
        (BinaryOp::Equal, Value::Integer(left), Value::Integer(right)) => {
            Some(Value::Bool(left == right))
        }
        (BinaryOp::NotEqual, Value::Integer(left), Value::Integer(right)) => {
            Some(Value::Bool(left != right))
        }
        _ => None,
    }
}

/// The compile-time functions, by module and name. They are taken out of
/// the modules before anything after expansion reads them (LR23.1).
type Helpers = BTreeMap<(ModuleId, String), Function>;

#[derive(Clone, Copy)]
struct Program<'a> {
    graph: &'a Graph,
    names: &'a Names,
    helpers: &'a Helpers,
}

pub fn expand(graph: &mut Graph, names: &Names, sources: &mut SourceMap) -> Vec<Diagnostic> {
    let modules: Vec<ModuleId> = graph.modules().map(|(id, _)| id).collect();
    let mut diagnostics = Vec::new();

    let helpers: Helpers = modules
        .iter()
        .flat_map(|&module| {
            graph
                .module(module)
                .ast
                .items
                .iter()
                .filter_map(move |item| match item {
                    Item::Function(function)
                        if function.name.len() == 1 && compile_time(function) =>
                    {
                        Some(((module, function.name[0].clone()), function.clone()))
                    }
                    _ => None,
                })
        })
        .collect();

    for module in modules {
        let program = Program {
            graph,
            names,
            helpers: &helpers,
        };
        let items = graph.module(module).ast.items.clone();
        let mut expanded = Vec::with_capacity(items.len());
        for mut item in items {
            if let Item::Function(function) = &item
                && compile_time(function)
            {
                continue;
            }
            let changes = expand_item(&mut item, module, program, sources, &mut diagnostics);
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
    program: Program<'_>,
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
        program,
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
    program: Program<'_>,
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
                let Some((origin, declaration)) = declaration(module, name, program) else {
                    arguments.push(argument);
                    continue;
                };
                let application = Application {
                    declaration,
                    module: origin,
                    arguments: &[],
                    span: argument.span,
                };
                let (added, reported) = Evaluator::run(target, program, sources, application);
                changes.extend(added);
                diagnostics.extend(reported);
            }
            decorator.args = arguments;
            if !decorator.args.is_empty() {
                retained.push(decorator);
            }
        } else if builtin(&decorator.name) {
            retained.push(decorator);
        } else if let Some((origin, declaration)) = declaration(module, &decorator.name, program) {
            let application = Application {
                declaration,
                module: origin,
                arguments: &decorator.args,
                span: decorator.span,
            };
            let (added, reported) = Evaluator::run(target, program, sources, application);
            changes.extend(added);
            diagnostics.extend(reported);
        } else {
            retained.push(decorator);
        }
    }

    *decorators = retained;
    changes
}

/// The decorator `name` reaches from `module`, and the module declaring it.
fn declaration<'a>(
    module: ModuleId,
    name: &str,
    program: Program<'a>,
) -> Option<(ModuleId, &'a DecoratorDecl)> {
    let binding = program.names.scope(module).get(name)?;
    let (origin, name) = match &binding.origin {
        Origin::Declared { .. } => (module, name),
        Origin::Imported { module, name } => (*module, name.as_str()),
        Origin::Binding { .. } | Origin::Namespace(_) => return None,
    };
    program
        .graph
        .module(origin)
        .ast
        .items
        .iter()
        .find_map(|item| match item {
            Item::DecoratorDecl(declaration) if declaration.name == name => {
                Some((origin, declaration))
            }
            _ => None,
        })
}

/// LR23.1: a function whose signature names a metadata type exists only
/// while a decorator runs.
fn compile_time(function: &Function) -> bool {
    function
        .params
        .iter()
        .filter_map(|param| param.ty.as_ref())
        .chain(function.result.as_ref())
        .any(names_metadata)
}

fn names_metadata(ty: &Type) -> bool {
    match &ty.kind {
        TypeKind::Path { segments, args } => {
            matches!(
                segments.as_slice(),
                [name] if matches!(
                    name.as_str(),
                    "TypeDeclaration" | "DeclarationField" | "DeclarationVariant"
                )
            ) || args.iter().any(names_metadata)
        }
        TypeKind::Optional(inner) | TypeKind::Pointer { target: inner, .. } => {
            names_metadata(inner)
        }
        TypeKind::Union(types) | TypeKind::Intersection(types) | TypeKind::Tuple(types) => {
            types.iter().any(names_metadata)
        }
        TypeKind::Function { params, result, .. } => {
            params.iter().any(names_metadata) || names_metadata(result)
        }
        TypeKind::Array { element, .. } => names_metadata(element),
        TypeKind::Record(fields) => fields.iter().any(|field| names_metadata(&field.ty)),
        TypeKind::Error => false,
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
