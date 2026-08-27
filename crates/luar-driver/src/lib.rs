//! Drives one compilation: source in, artifact or diagnostics out.

mod graph;

use luar_diagnostics::{Diagnostic, FileId, SourceMap};

/// What checking a module produced.
#[derive(Debug)]
pub enum Check {
    /// The frontend ran. An empty list means the program was accepted.
    Ran(Vec<Diagnostic>),
    /// The frontend does not exist yet.
    ///
    /// This is not acceptance. Anything reading a `Check` must treat it as "no
    /// answer", so that an unbuilt compiler cannot report a program as valid.
    /// The variant goes away when the frontend lands.
    Unimplemented,
}

/// Checks `root` and the modules it imports, without producing an artifact.
///
/// The frontend reaches as far as the top-level names of each module: every
/// module the root imports is read and parsed, an import naming nothing is
/// reported, and so is one naming something the other module does not export.
/// Each stage added after this one narrows what an accepted program is: the
/// rest of name resolution, then type checking. A program accepted here and
/// rejected later was never accepted by the finished compiler, and the test
/// that says so starts failing the day the stage that rejects it lands.
///
/// Imported modules are added to `sources`, so their spans resolve like the
/// root's.
#[must_use]
pub fn check(sources: &mut SourceMap, root: FileId) -> Check {
    let (graph, mut diagnostics) = graph::build(sources, root);
    let (names, reported) = luar_sema::names::resolve(&graph);
    diagnostics.extend(reported);

    let (reported, uses) = luar_sema::scope::resolve(&graph, &names);
    diagnostics.extend(reported);
    diagnostics.extend(luar_sema::init::check(&graph, &uses));

    let (mut table, reported) = luar_sema::table::build(&graph, &names);
    diagnostics.extend(reported);
    // LR7: a function that writes no result gets one worked out before
    // anything is reported, because the calls to it read what it gives back.
    luar_sema::check::infer_results(&graph, &names, &mut table);
    let (_facts, reported) = luar_sema::check::check(&graph, &names, &table);
    diagnostics.extend(reported);
    Check::Ran(diagnostics)
}
