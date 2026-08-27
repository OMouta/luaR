//! What each module declares, exports, and imports (LR21, LR21.1).

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

use luar_ast::{Binding as Bound, Import, ImportNames, Item, StmtKind};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::modules::{Graph, ModuleId, Node};

/// A name at a module's top level, and where it came from.
#[derive(Debug, Clone)]
pub struct Binding {
    pub origin: Origin,
    /// Where the name was bound: the declaration, or the import naming it.
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Origin {
    /// Declared in this module. Private to it unless exported (LR21).
    Declared { exported: bool },
    /// A module-level `local` or `const` (LR21.3), in scope from where it is
    /// written onward rather than throughout. Only a `const` is exportable
    /// (LR52), and only a `const` may be read while compiling (LR24).
    Binding { exported: bool, constant: bool },
    /// One name from another module, under the name it has here, which `as`
    /// may have changed (LR21.1).
    Imported { module: ModuleId, name: String },
    /// A whole module, bound to a name (LR21.1).
    Namespace(ModuleId),
}

/// Whether an origin puts its name on the module surface (LR21).
fn exported(origin: &Origin) -> bool {
    matches!(
        origin,
        Origin::Declared { exported: true } | Origin::Binding { exported: true, .. }
    )
}

/// The top-level names of one module.
#[derive(Debug, Default)]
pub struct Scope {
    names: BTreeMap<String, Binding>,
}

impl Scope {
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Binding> {
        self.names.get(name)
    }

    pub fn names(&self) -> impl Iterator<Item = (&str, &Binding)> {
        self.names
            .iter()
            .map(|(name, binding)| (name.as_str(), binding))
    }

    /// Whether an importing module may name `name` (LR21).
    #[must_use]
    pub fn exports(&self, name: &str) -> bool {
        self.get(name)
            .is_some_and(|binding| exported(&binding.origin))
    }

    /// Binds `name`, unless it is already bound.
    fn bind(&mut self, name: String, binding: Binding) {
        match self.names.entry(name) {
            Entry::Vacant(slot) => {
                slot.insert(binding);
            }
            Entry::Occupied(mut slot) => {
                if exported(&binding.origin) && !exported(&slot.get().origin) {
                    slot.insert(binding);
                }
            }
        }
    }
}

/// Every module's top-level names.
#[derive(Debug, Default)]
pub struct Names {
    scopes: BTreeMap<ModuleId, Scope>,
}

impl Names {
    /// # Panics
    #[must_use]
    pub fn scope(&self, module: ModuleId) -> &Scope {
        self.scopes
            .get(&module)
            .expect("module id belongs to another graph")
    }
}

/// Binds the top-level names of every module in `graph`.
#[must_use]
pub fn resolve(graph: &Graph) -> (Names, Vec<Diagnostic>) {
    let mut names = Names::default();
    for (id, node) in graph.modules() {
        names.scopes.insert(id, declared(node));
    }

    let mut diagnostics = Vec::new();
    let imported: Vec<(ModuleId, Vec<(String, Binding)>)> = graph
        .modules()
        .map(|(id, node)| (id, imported(node, &names, &mut diagnostics)))
        .collect();

    for (id, bindings) in imported {
        let scope = names.scopes.get_mut(&id).expect("every module has a scope");
        for (name, binding) in bindings {
            scope.bind(name, binding);
        }
    }

    (names, diagnostics)
}

/// The names a module declares, and whether each is exported.
fn declared(node: &Node) -> Scope {
    let mut scope = Scope::default();
    declarations(&node.ast.items, &mut scope);
    scope
}

/// Collects declarations, including the ones inside `#if` (LR48).
fn declarations(items: &[Item], scope: &mut Scope) {
    for item in items {
        let (name, exported, span) = match item {
            // A qualified name declares a member of a type (LR20, LR42), not a
            // name of its own.
            Item::Function(f) if f.name.len() == 1 => (&f.name[0], f.exported, f.span),
            Item::Struct(s) => (&s.name, s.exported, s.span),
            Item::Enum(e) => (&e.name, e.exported, e.span),
            Item::Interface(i) => (&i.name, i.exported, i.span),
            Item::Extend(e) => (&e.name, e.exported, e.span),
            Item::TypeAlias(a) => (&a.name, a.exported, a.span),
            Item::Conditional(conditional) => {
                for (_, items) in &conditional.branches {
                    declarations(items, scope);
                }
                if let Some(items) = &conditional.otherwise {
                    declarations(items, scope);
                }
                continue;
            }
            // A module-level binding is a name of the module too (LR21.3), and
            // a `const` may be exported (LR52).
            Item::Stmt(stmt) => {
                let (binding, exported, constant) = match &stmt.kind {
                    StmtKind::Local { binding, .. } => (binding, false, false),
                    StmtKind::Const {
                        binding, exported, ..
                    } => (binding, *exported, true),
                    _ => continue,
                };

                for name in bound(binding) {
                    scope.bind(
                        name,
                        Binding {
                            origin: Origin::Binding { exported, constant },
                            span: stmt.span,
                        },
                    );
                }
                continue;
            }
            _ => continue,
        };

        scope.bind(
            name.clone(),
            Binding {
                origin: Origin::Declared { exported },
                span,
            },
        );
    }
}

/// The names a module's imports bring in, reporting the ones the other module
/// does not export.
fn imported(
    node: &Node,
    names: &Names,
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<(String, Binding)> {
    let mut bindings = Vec::new();

    for (import, edge) in imports(node).zip(&node.imports) {
        // An import that reached nothing is reported where it was resolved,
        // and there is no module to ask what it exports.
        let Some(module) = edge.target else { continue };

        match &import.names {
            ImportNames::Namespace(name) => bindings.push((
                name.clone(),
                Binding {
                    origin: Origin::Namespace(module),
                    span: import.span,
                },
            )),
            ImportNames::Named(imported) => {
                for name in imported {
                    if !names.scope(module).exports(&name.name) {
                        diagnostics
                            .push(not_exported(import, &name.name, name.span, names, module));
                    }

                    let local = name.alias.clone().unwrap_or_else(|| name.name.clone());
                    bindings.push((
                        local,
                        Binding {
                            origin: Origin::Imported {
                                module,
                                name: name.name.clone(),
                            },
                            span: name.span,
                        },
                    ));
                }
            }
        }
    }

    bindings
}

fn not_exported(
    import: &Import,
    name: &str,
    span: Span,
    names: &Names,
    module: ModuleId,
) -> Diagnostic {
    let from = import.path.as_deref().unwrap_or_default();

    if names.scope(module).get(name).is_some() {
        Diagnostic::error(
            codes::NAME_NOT_EXPORTED,
            span,
            format!("`{name}` is declared in `{from}`, and not exported"),
        )
        .note("A declaration is private to its module unless it is exported (LR21).")
    } else {
        Diagnostic::error(
            codes::NAME_NOT_EXPORTED,
            span,
            format!("`{from}` has nothing named `{name}`"),
        )
    }
}

/// A module's imports, in the order written, which is the order its edges are
/// in (see [`Node::imports`]).
fn imports(node: &Node) -> impl Iterator<Item = &Import> {
    node.ast.items.iter().filter_map(|item| match item {
        Item::Import(import) => Some(import),
        _ => None,
    })
}

/// The names a binding binds, in the order written (LR5.3).
pub(crate) fn bound(binding: &Bound) -> Vec<String> {
    match binding {
        Bound::Name(name) => vec![name.clone()],
        Bound::Record(fields) => fields
            .iter()
            .map(|field| {
                field
                    .bound_as
                    .clone()
                    .unwrap_or_else(|| field.field.clone())
            })
            .collect(),
        Bound::Tuple(bindings) => bindings.iter().flat_map(bound).collect(),
        Bound::Error => Vec::new(),
    }
}
