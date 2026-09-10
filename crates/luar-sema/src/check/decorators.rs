//! Resolving package-defined decorator names (LR23.1).

use luar_ast::{Decorator, ExprKind, Function, InterfaceMember, Item, Member};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin};
use crate::table::{Decl, Table};
use crate::types::Type;

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
            decorators(&function.decorators, module, names, table, diagnostics);
            test(
                &function.decorators,
                valid_test(function, module, table),
                diagnostics,
            );
        }
        Item::Struct(structure) => {
            test(&structure.decorators, false, diagnostics);
            decorators(&structure.decorators, module, names, table, diagnostics);
            for member in &structure.members {
                if let Member::Function { function, .. } = member {
                    test(&function.decorators, false, diagnostics);
                    decorators(&function.decorators, module, names, table, diagnostics);
                }
            }
        }
        Item::Enum(enumeration) => {
            test(&enumeration.decorators, false, diagnostics);
            decorators(&enumeration.decorators, module, names, table, diagnostics)
        }
        Item::Interface(interface) => {
            test(&interface.decorators, false, diagnostics);
            decorators(&interface.decorators, module, names, table, diagnostics);
            for member in &interface.members {
                if let InterfaceMember::Function(function) = member {
                    test(&function.decorators, false, diagnostics);
                    decorators(&function.decorators, module, names, table, diagnostics);
                }
            }
        }
        Item::Extend(extend) => {
            test(&extend.decorators, false, diagnostics);
            decorators(&extend.decorators, module, names, table, diagnostics);
            for function in &extend.functions {
                test(&function.decorators, false, diagnostics);
                decorators(&function.decorators, module, names, table, diagnostics);
            }
        }
        Item::TypeAlias(alias) => {
            test(&alias.decorators, false, diagnostics);
            decorators(&alias.decorators, module, names, table, diagnostics);
        }
        Item::Import(_) | Item::DecoratorDecl(_) | Item::Stmt(_) => {}
    }
}

fn valid_test(function: &Function, module: ModuleId, table: &Table) -> bool {
    function.name.len() == 1
        && function.body.is_some()
        && function.params.is_empty()
        && function.type_params.is_empty()
        && !function.unsafe_
        && !function
            .decorators
            .iter()
            .any(|decorator| decorator.name == "extern")
        && table
            .overloads(module, &function.name[0])
            .is_some_and(|overloads| {
                overloads.iter().any(|signature| {
                    signature.span == function.span
                        && matches!(&signature.result, Type::Tuple(items) if items.is_empty())
                })
            })
}

fn test(applied: &[Decorator], valid: bool, diagnostics: &mut Vec<Diagnostic>) {
    let mut seen = false;
    for decorator in applied.iter().filter(|decorator| decorator.name == "test") {
        if !valid || !decorator.args.is_empty() || seen {
            diagnostics.push(Diagnostic::error(
                codes::TEST_DECLARATION,
                decorator.span,
                "`@test` requires a parameterless module function returning `()`",
            ));
        }
        seen = true;
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
