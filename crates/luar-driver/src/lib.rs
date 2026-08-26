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
/// The frontend reaches as far as the module graph: every module the root
/// imports is read and parsed, and an import naming nothing is reported. Each
/// stage added after this one narrows what an accepted program is: name
/// resolution, then type checking. A program accepted here and rejected later
/// was never accepted by the finished compiler, and the test that says so
/// starts failing the day the stage that rejects it lands.
///
/// Imported modules are added to `sources`, so their spans resolve like the
/// root's.
#[must_use]
pub fn check(sources: &mut SourceMap, root: FileId) -> Check {
    let (_graph, diagnostics) = graph::build(sources, root);
    Check::Ran(diagnostics)
}
