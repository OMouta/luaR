//! Reading a program: the root module, and everything it imports (LR21.1).

use std::collections::VecDeque;
use std::fs;
use std::path::Path;

use luar_ast::{Import, Item};
use luar_diagnostics::{Diagnostic, FileId, SourceMap, Span, codes};
use luar_parser::Target;
use luar_sema::modules::{Edge, Graph, Missing, ModuleId, PRELUDE};

/// The standard library, one module per source file under `std/` (LR60).
const STD: &[(&str, &str)] = &[
    ("std/env", include_str!("../../../std/env.luar")),
    ("std/fs", include_str!("../../../std/fs.luar")),
    ("std/mem", include_str!("../../../std/mem.luar")),
    ("std/prelude", include_str!("../../../std/prelude.luar")),
    ("std/thread", include_str!("../../../std/thread.luar")),
];

/// Reads and parses `root` and everything reachable from it.
pub(crate) fn build(
    sources: &mut SourceMap,
    root: FileId,
    target: Target,
) -> (Graph, Vec<Diagnostic>) {
    let mut graph = Graph::default();
    let mut diagnostics = Vec::new();

    let path = luar_sema::modules::normalize(sources.file(root).path().to_path_buf());
    let text = sources.file(root).text().to_owned();
    let parsed = luar_parser::module_for(&text, root, target);
    diagnostics.extend(parsed.diagnostics);

    let mut queue = VecDeque::from([graph.insert(root, path, parsed.tree)]);
    let prelude = standard(
        PRELUDE,
        target,
        sources,
        &mut graph,
        &mut queue,
        &mut diagnostics,
    )
    .expect("the prelude ships with the compiler");

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
                target,
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
    graph.open_prelude(prelude);

    (graph, diagnostics)
}

/// Resolves one import and reads what it names, unless the graph already has
/// it. Returns the module it reached, and `None` once the failure is reported.
fn read(
    import: &Import,
    target: Target,
    importer: &Path,
    sources: &mut SourceMap,
    graph: &mut Graph,
    queue: &mut VecDeque<ModuleId>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<ModuleId> {
    // A path the parser could not read is already reported, and guessing at
    // what was meant would report it twice.
    let path = import.path.as_deref()?;

    if STD.iter().any(|(name, _)| *name == path) {
        return standard(path, target, sources, graph, queue, diagnostics);
    }

    let file = match luar_sema::modules::resolve(path, importer) {
        luar_sema::modules::Target::File(file) => file,
        luar_sema::modules::Target::Missing(why) => {
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
    let parsed = luar_parser::module_for(sources.file(id).text(), id, target);
    diagnostics.extend(parsed.diagnostics);

    let module = graph.insert(id, file, parsed.tree);
    queue.push_back(module);
    Some(module)
}

/// Reads the standard library module `path` names, unless the graph already
/// has it (LR60).
fn standard(
    path: &str,
    target: Target,
    sources: &mut SourceMap,
    graph: &mut Graph,
    queue: &mut VecDeque<ModuleId>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<ModuleId> {
    let (_, source) = STD.iter().find(|(name, _)| *name == path)?;
    let file = Path::new(path).to_path_buf();
    if let Some(known) = graph.find(&file) {
        return Some(known);
    }

    let id = sources.add(file.clone(), *source);
    let parsed = luar_parser::module_for(sources.file(id).text(), id, target);
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
             module, as in `std/fs`, or a package, as in `http/client` (LR21.1).",
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
