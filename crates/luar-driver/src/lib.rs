//! Drives one compilation: source in, artifact or diagnostics out.

mod graph;

use std::path::Path;

use luar_diagnostics::{Diagnostic, FileId, SourceMap};
use luar_lir::lower::Lowered;

pub use luar_lir::lower::CompilationMode;

/// What checking a module produced.
#[derive(Debug)]
pub enum Check {
    /// The frontend ran. An empty list means the program was accepted.
    Ran(Vec<Diagnostic>),
    /// The frontend does not exist yet.
    Unimplemented,
}

/// Checks `root` and the modules it imports, without producing an artifact.
#[must_use]
pub fn check(sources: &mut SourceMap, root: FileId) -> Check {
    Check::Ran(frontend(sources, root).diagnostics)
}

/// Checks `root` and lowers what was accepted to LIR.
pub fn lower(sources: &mut SourceMap, root: FileId) -> Result<Lowered, Vec<Diagnostic>> {
    lower_in_mode(sources, root, CompilationMode::Debug)
}

pub fn lower_in_mode(
    sources: &mut SourceMap,
    root: FileId,
    mode: CompilationMode,
) -> Result<Lowered, Vec<Diagnostic>> {
    let checked = frontend(sources, root);
    if checked.diagnostics.iter().any(Diagnostic::is_error) {
        return Err(checked.diagnostics);
    }
    let mut lowered =
        luar_lir::lower::lower_in_mode(&checked.graph, &checked.table, &checked.facts, mode);
    // LR18.1: an interface call that can reach one function only is a call to
    // that function, which is a question about the whole program.
    luar_lir::devirt::run(&mut lowered.program);
    // LR19: a generic function is a template until a call says what fills it,
    // so this runs over the whole program rather than one module at a time.
    luar_lir::mono::run(&mut lowered.program);
    luar_lir::inline::run(&mut lowered.program);
    luar_lir::bounds::run(&mut lowered.program);
    Ok(lowered)
}

/// Why a build produced no executable.
#[derive(Debug)]
pub enum BuildError {
    /// The program was rejected.
    Rejected(Vec<Diagnostic>),
    /// The program was accepted, and lowering does not cover all of it.
    NotLowered(Vec<luar_lir::lower::Gap>),
    /// The program lowered, and the backend does not cover all of it.
    NotEmitted(Vec<luar_codegen::Gap>),
    Backend(luar_codegen::Error),
    Link(luar_codegen::LinkError),
    Io(std::io::Error),
}

/// Compiles `root` and the modules it imports into an executable at
/// `output`.
///
/// # Errors
/// Returns [`BuildError`] where the program is rejected, where a stage does
/// not cover all of it, or where the linker fails.
pub fn build(sources: &mut SourceMap, root: FileId, output: &Path) -> Result<(), BuildError> {
    build_in_mode(sources, root, output, CompilationMode::Debug)
}

pub fn build_in_mode(
    sources: &mut SourceMap,
    root: FileId,
    output: &Path,
    mode: CompilationMode,
) -> Result<(), BuildError> {
    let lowered = lower_in_mode(sources, root, mode).map_err(BuildError::Rejected)?;
    if !lowered.gaps.is_empty() {
        return Err(BuildError::NotLowered(lowered.gaps));
    }

    let object = luar_codegen::compile(&lowered.program).map_err(BuildError::Backend)?;
    if !object.gaps.is_empty() {
        return Err(BuildError::NotEmitted(object.gaps));
    }

    let path = output.with_extension("o");
    std::fs::write(&path, &object.bytes).map_err(BuildError::Io)?;
    let linked = luar_codegen::link(&path, output);
    // The object is an intermediate, and a failed link has already said
    // everything the file could.
    let _ = std::fs::remove_file(&path);
    linked.map_err(BuildError::Link)
}

/// What the frontend produced: everything a later stage reads, and what it
/// reported.
struct Frontend {
    graph: luar_sema::modules::Graph,
    table: luar_sema::table::Table,
    facts: luar_sema::facts::Facts,
    diagnostics: Vec<Diagnostic>,
}

fn frontend(sources: &mut SourceMap, root: FileId) -> Frontend {
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
    let (facts, reported) = luar_sema::check::check(&graph, &names, &table);
    diagnostics.extend(reported);

    Frontend {
        graph,
        table,
        facts,
        diagnostics,
    }
}
