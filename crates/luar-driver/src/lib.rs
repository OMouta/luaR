//! Drives one compilation: source in, artifact or diagnostics out.

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
/// Only the lexer exists, so this can answer one of the two questions. A
/// program the lexer rejects is rejected, and the diagnostics say why. A
/// program it accepts has only been lexed, and calling that acceptance would
/// report every unparsed and unchecked program as valid, so it reports no
/// answer instead.
#[must_use]
pub fn check(sources: &SourceMap, root: FileId) -> Check {
    let lexed = luar_lexer::lex(sources.file(root).text(), root);

    if lexed.diagnostics.iter().any(Diagnostic::is_error) {
        Check::Ran(lexed.diagnostics)
    } else {
        Check::Unimplemented
    }
}
