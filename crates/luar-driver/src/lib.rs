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
#[must_use]
pub fn check(_sources: &SourceMap, _root: FileId) -> Check {
    Check::Unimplemented
}
