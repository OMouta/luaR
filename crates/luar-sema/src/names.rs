//! What each module declares, exports, and imports (§21, §21.1).
//!
//! A module's top level is a set of names. Some are declared there, some are
//! brought in by an import, and an import may bind a name that is not the one
//! the other module used, because `as` renames it. This builds that set for
//! every module in the graph, and reports an import that names something the
//! other module keeps to itself.
//!
//! Only declarations are bound here. Module-level `local` and `const`
//! bindings (§21.3) are names too, and they arrive with the rest of lexical
//! scoping (§54).

use std::collections::BTreeMap;

use luar_ast::{Import, ImportNames, Item};
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
    /// Declared in this module. Private to it unless exported (§21).
    Declared { exported: bool },
    /// One name from another module, under the name it has here, which `as`
    /// may have changed (§21.1).
    Imported { module: ModuleId, name: String },
    /// A whole module, bound to a name (§21.1).
    Namespace(ModuleId),
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

    /// Whether an importing module may name `name` (§21).
    #[must_use]
    pub fn exports(&self, name: &str) -> bool {
        matches!(
            self.get(name).map(|binding| &binding.origin),
            Some(Origin::Declared { exported: true })
        )
    }

    /// Binds `name`, unless it is already bound.
    ///
    /// Two declarations of one name at module level is not a rule stated yet,
    /// and keeping the first is what makes the later stages see one binding
    /// rather than the last one written.
    fn bind(&mut self, name: String, binding: Binding) {
        self.names.entry(name).or_insert(binding);
    }
}

/// Every module's top-level names.
#[derive(Debug, Default)]
pub struct Names {
    scopes: BTreeMap<ModuleId, Scope>,
}

impl Names {
    /// # Panics
    ///
    /// Panics if `module` came from another graph.
    #[must_use]
    pub fn scope(&self, module: ModuleId) -> &Scope {
        self.scopes
            .get(&module)
            .expect("module id belongs to another graph")
    }
}

/// Binds the top-level names of every module in `graph`.
///
/// Declarations are collected first, across all modules, because an import
/// can only be checked against a module whose declarations are known.
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

/// Collects declarations, including the ones inside `#if` (§48).
///
/// Every branch contributes. Which one the target selects is decided later,
/// and a name that only one branch declares is still a name this module can
/// declare, so leaving the others out would report uses of them as unknown.
fn declarations(items: &[Item], scope: &mut Scope) {
    for item in items {
        let (name, exported, span) = match item {
            // A qualified name declares a member of a type (§20, §42), not a
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
///
/// A name that is not exported is bound anyway. It is already reported, and
/// binding it keeps one mistake from being reported again everywhere the name
/// is used.
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
        .note("A declaration is private to its module unless it is exported (§21).")
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
