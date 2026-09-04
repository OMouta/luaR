//! Reading a program: the root module, and everything it imports (LR21.1).

use std::collections::VecDeque;
use std::fs;
use std::path::Path;

use luar_ast::{Import, Item};
use luar_diagnostics::{Diagnostic, FileId, SourceMap, Span, codes};
use luar_parser::Target;
use luar_sema::modules::{Edge, Graph, Missing, ModuleId, PRELUDE};

use crate::packages::Packages;

/// The standard library, one module per source file under `std/` (LR60).
const STD: &[(&str, &str)] = &[
    (
        "std/collections",
        include_str!("../../../std/collections.luar"),
    ),
    ("std/env", include_str!("../../../std/env.luar")),
    ("std/fs", include_str!("../../../std/fs.luar")),
    ("std/math", include_str!("../../../std/math.luar")),
    ("std/mem", include_str!("../../../std/mem.luar")),
    ("std/prelude", include_str!("../../../std/prelude.luar")),
    ("std/process", include_str!("../../../std/process.luar")),
    ("std/random", include_str!("../../../std/random.luar")),
    ("std/testing", include_str!("../../../std/testing.luar")),
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
    let mut packages = Packages::default();

    let path = luar_sema::modules::normalize(sources.file(root).path().to_path_buf());
    let package = match packages.root(&mut graph, &path) {
        Ok(package) => package,
        Err(message) => {
            diagnostics.push(Diagnostic::error(
                codes::UNRESOLVED_IMPORT,
                Span::at(root, 0),
                message,
            ));
            graph.loose_package()
        }
    };
    let text = sources.file(root).text().to_owned();
    let parsed = luar_parser::module_for(&text, root, target);
    diagnostics.extend(parsed.diagnostics);

    let mut queue = VecDeque::from([graph.insert(root, path, package, parsed.tree)]);
    let standard_package = graph.add_package(luar_sema::modules::Package {
        name: "std".to_owned(),
        version: env!("CARGO_PKG_VERSION").to_owned(),
        source: Path::new("std").to_path_buf(),
    });
    let prelude = standard(
        PRELUDE,
        target,
        standard_package,
        sources,
        &mut graph,
        &mut queue,
        &mut diagnostics,
    )
    .expect("the prelude ships with the compiler");

    {
        let mut state = ReadState {
            sources,
            graph: &mut graph,
            queue: &mut queue,
            diagnostics: &mut diagnostics,
        };
        while let Some(id) = state.queue.pop_front() {
            let importer = state.graph.module(id).path.clone();
            let importer_package = state.graph.module(id).package;
            let imports: Vec<Import> = state
                .graph
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
                    importer_package,
                    standard_package,
                    &mut packages,
                    &mut state,
                );
                edges.push(Edge {
                    target,
                    span: import.path_span,
                });
            }
            state.graph.set_imports(id, edges);
        }
    }
    graph.open_prelude(prelude);

    (graph, diagnostics)
}

struct ReadState<'a> {
    sources: &'a mut SourceMap,
    graph: &'a mut Graph,
    queue: &'a mut VecDeque<ModuleId>,
    diagnostics: &'a mut Vec<Diagnostic>,
}

/// Resolves one import and reads what it names, unless the graph already has
/// it. Returns the module it reached, and `None` once the failure is reported.
fn read(
    import: &Import,
    target: Target,
    importer: &Path,
    importer_package: luar_sema::modules::PackageId,
    standard_package: luar_sema::modules::PackageId,
    packages: &mut Packages,
    state: &mut ReadState<'_>,
) -> Option<ModuleId> {
    // A path the parser could not read is already reported, and guessing at
    // what was meant would report it twice.
    let path = import.path.as_deref()?;

    if STD.iter().any(|(name, _)| *name == path) {
        return standard(
            path,
            target,
            standard_package,
            state.sources,
            state.graph,
            state.queue,
            state.diagnostics,
        );
    }

    let (file, package) = match luar_sema::modules::classify(path) {
        Some(luar_sema::modules::Specifier::Package { name, module }) => {
            match packages.resolve(state.graph, importer_package, name, module) {
                Ok(resolved) => resolved,
                Err(message) => {
                    state.diagnostics.push(Diagnostic::error(
                        codes::UNRESOLVED_IMPORT,
                        import.path_span,
                        message,
                    ));
                    return None;
                }
            }
        }
        _ => match luar_sema::modules::resolve(path, importer) {
            luar_sema::modules::Target::File(file) => (file, importer_package),
            luar_sema::modules::Target::Missing(why) => {
                state.diagnostics.push(missing(import, why));
                return None;
            }
        },
    };

    if let Some(known) = state.graph.find(&file) {
        return Some(known);
    }

    let text = match fs::read_to_string(&file) {
        Ok(text) => text,
        Err(e) => {
            state
                .diagnostics
                .push(unreadable(import.path_span, &file, &e));
            return None;
        }
    };

    let id = state.sources.add(file.clone(), text);
    let parsed = luar_parser::module_for(state.sources.file(id).text(), id, target);
    state.diagnostics.extend(parsed.diagnostics);

    let module = state.graph.insert(id, file, package, parsed.tree);
    state.queue.push_back(module);
    Some(module)
}

/// Reads the standard library module `path` names, unless the graph already
/// has it (LR60).
fn standard(
    path: &str,
    target: Target,
    package: luar_sema::modules::PackageId,
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

    let module = graph.insert(id, file, package, parsed.tree);
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
