//! Resolving package-defined decorator names (LR23.1).

use luar_ast::{Decorator, ExprKind, InterfaceMember, Item, Member};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin};
use crate::table::{Decl, Table};

pub(super) fn check(graph: &Graph, names: &Names, table: &Table) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for (module, node) in graph.modules() {
        for item in &node.ast.items {
            visit(item, module, names, table, &mut diagnostics);
        }
    }
    diagnostics
}

fn visit(
    item: &Item,
    module: ModuleId,
    names: &Names,
    table: &Table,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match item {
        Item::Function(function) => {
            decorators(&function.decorators, module, names, table, diagnostics)
        }
        Item::Struct(structure) => {
            decorators(&structure.decorators, module, names, table, diagnostics);
            for member in &structure.members {
                if let Member::Function { function, .. } = member {
                    decorators(&function.decorators, module, names, table, diagnostics);
                }
            }
        }
        Item::Enum(enumeration) => {
            decorators(&enumeration.decorators, module, names, table, diagnostics)
        }
        Item::Interface(interface) => {
            decorators(&interface.decorators, module, names, table, diagnostics);
            for member in &interface.members {
                if let InterfaceMember::Function(function) = member {
                    decorators(&function.decorators, module, names, table, diagnostics);
                }
            }
        }
        Item::Extend(extend) => {
            decorators(&extend.decorators, module, names, table, diagnostics);
            for function in &extend.functions {
                decorators(&function.decorators, module, names, table, diagnostics);
            }
        }
        Item::TypeAlias(alias) => decorators(&alias.decorators, module, names, table, diagnostics),
        Item::Import(_) | Item::DecoratorDecl(_) | Item::Stmt(_) => {}
    }
}

fn decorators(
    applied: &[Decorator],
    module: ModuleId,
    names: &Names,
    table: &Table,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for decorator in applied {
        if decorator.name == "derive" {
            for argument in &decorator.args {
                let ExprKind::Name(name) = &argument.value.kind else {
                    continue;
                };
                if !matches!(name.as_str(), "Eq" | "Hash" | "Display") {
                    resolve(name, argument.value.span, module, names, table, diagnostics);
                }
            }
        } else if !builtin(&decorator.name) {
            resolve(
                &decorator.name,
                decorator.span,
                module,
                names,
                table,
                diagnostics,
            );
        }
    }
}

fn resolve(
    name: &str,
    span: Span,
    module: ModuleId,
    names: &Names,
    table: &Table,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let declared = names
        .scope(module)
        .get(name)
        .and_then(|binding| match &binding.origin {
            Origin::Declared { .. } => Some((module, name)),
            Origin::Imported { module, name } => Some((*module, name.as_str())),
            Origin::Binding { .. } | Origin::Namespace(_) => None,
        });
    if declared.is_some_and(|(module, name)| {
        matches!(table.get(module, name), Some(Decl::Decorator { .. }))
    }) {
        return;
    }

    diagnostics.push(
        Diagnostic::error(
            codes::DECORATOR_NOT_FOUND,
            span,
            format!("`{name}` does not name a decorator in scope"),
        )
        .note("Import a package decorator before applying it (LR23.1)."),
    );
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
