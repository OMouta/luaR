//! Reading a program: the root module, and everything it imports (§21.1).
//!
//! Modules are read breadth first from the root. A module already in the
//! graph is not read again, which is both what makes a cycle terminate here
//! and what §21.2 requires of initialization.

use std::collections::VecDeque;
use std::fs;
use std::path::Path;

use luar_ast::{Import, Item};
use luar_diagnostics::{Diagnostic, FileId, SourceMap, Span, codes};
use luar_sema::modules::{Edge, Graph, Missing, ModuleId, Target};

/// Reads and parses `root` and everything reachable from it.
pub(crate) fn build(sources: &mut SourceMap, root: FileId) -> (Graph, Vec<Diagnostic>) {
    let mut graph = Graph::default();
    let mut diagnostics = Vec::new();

    let path = sources.file(root).path().to_path_buf();
    let text = sources.file(root).text().to_owned();
    let parsed = luar_parser::module(&text, root);
    diagnostics.extend(parsed.diagnostics);

    let mut queue = VecDeque::from([graph.insert(root, path, parsed.tree)]);

    while let Some(id) = queue.pop_front() {
        let importer = graph.module(id).path.clone();
        let imports: Vec<Import> = graph
            .module(id)
            .ast
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Import(import) => Some(import.clone()),
                _ => None,
            })
            .collect();

        let mut edges = Vec::with_capacity(imports.len());
        for import in imports {
            let target = read(
                &import,
                &importer,
                sources,
                &mut graph,
                &mut queue,
                &mut diagnostics,
            );
            edges.push(Edge {
                target,
                span: import.path_span,
            });
        }
        graph.set_imports(id, edges);
    }

    (graph, diagnostics)
}

/// Resolves one import and reads what it names, unless the graph already has
/// it. Returns the module it reached, and `None` once the failure is reported.
///
/// Only a module read here is queued. A module already in the graph is
/// reached again by every import that names it, and queueing it each time is
/// how a cycle would never end.
fn read(
    import: &Import,
    importer: &Path,
    sources: &mut SourceMap,
    graph: &mut Graph,
    queue: &mut VecDeque<ModuleId>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<ModuleId> {
    // A path the parser could not read is already reported, and guessing at
    // what was meant would report it twice.
    let path = import.path.as_deref()?;

    let file = match luar_sema::modules::resolve(path, importer) {
        Target::File(file) => file,
        Target::Missing(why) => {
            diagnostics.push(missing(import, why));
            return None;
        }
    };

    if let Some(known) = graph.find(&file) {
        return Some(known);
    }

    let text = match fs::read_to_string(&file) {
        Ok(text) => text,
        Err(e) => {
            diagnostics.push(unreadable(import.path_span, &file, &e));
            return None;
        }
    };

    let id = sources.add(file.clone(), text);
    let parsed = luar_parser::module(sources.file(id).text(), id);
    diagnostics.extend(parsed.diagnostics);

    let module = graph.insert(id, file, parsed.tree);
    queue.push_back(module);
    Some(module)
}

fn missing(import: &Import, why: Missing) -> Diagnostic {
    let path = import.path.as_deref().unwrap_or_default();

    match why {
        Missing::Malformed => Diagnostic::error(
            codes::UNRESOLVED_IMPORT,
            import.path_span,
            format!("`{path}` does not name a module"),
        )
        .note(
            "A module path is relative, as in `./config`, a standard library \
             module, as in `std/fs`, or a package, as in `http/client` (§21.1).",
        ),
        Missing::StandardLibrary => Diagnostic::error(
            codes::UNRESOLVED_IMPORT,
            import.path_span,
            format!("`{path}` is a standard library module, and there is no standard library yet"),
        ),
        Missing::Package => Diagnostic::error(
            codes::UNRESOLVED_IMPORT,
            import.path_span,
            format!("`{path}` names a package, and packages are not resolved yet"),
        ),
    }
}

fn unreadable(span: Span, file: &Path, error: &std::io::Error) -> Diagnostic {
    let message = if error.kind() == std::io::ErrorKind::NotFound {
        format!("there is no module at `{}`", file.display())
    } else {
        format!("`{}` could not be read: {error}", file.display())
    };

    Diagnostic::error(codes::UNRESOLVED_IMPORT, span, message)
}
