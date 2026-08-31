//! Handing an object file to the system linker.
//!
//! v0 requires a linker to already be installed rather than shipping one.

use std::path::Path;
use std::process::Command;

#[derive(Debug)]
pub enum LinkError {
    /// No linker was found, and the message says where one was looked for.
    NotFound(String),
    /// The linker ran and could not be waited on.
    Failed(std::io::Error),
    /// The linker ran and reported an error, with whatever it wrote.
    Rejected(String),
}

impl std::fmt::Display for LinkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotFound(message) => write!(f, "no linker: {message}"),
            Self::Failed(error) => write!(f, "the linker did not run: {error}"),
            Self::Rejected(output) => write!(f, "the linker rejected the object:\n{output}"),
        }
    }
}

impl std::error::Error for LinkError {}

/// Links `object` into an executable at `output`.
///
/// # Errors
/// Returns [`LinkError`] where no linker is installed, where it cannot be
/// started, or where it rejects the object.
pub fn link(object: &Path, output: &Path) -> Result<(), LinkError> {
    let mut command = linker(object, output)?;
    let produced = command.output().map_err(LinkError::Failed)?;
    if produced.status.success() {
        return Ok(());
    }

    let mut message = String::from_utf8_lossy(&produced.stdout).into_owned();
    message.push_str(&String::from_utf8_lossy(&produced.stderr));
    Err(LinkError::Rejected(message))
}

#[cfg(windows)]
fn linker(object: &Path, output: &Path) -> Result<Command, LinkError> {
    let target = std::env::var("TARGET").unwrap_or_else(|_| "x86_64-pc-windows-msvc".to_owned());
    let mut command = cc::windows_registry::find(&target, "link.exe").ok_or_else(|| {
        LinkError::NotFound(
            "install the Visual Studio Build Tools with the C++ workload".to_owned(),
        )
    })?;

    command
        .arg("/NOLOGO")
        .arg("/SUBSYSTEM:CONSOLE")
        .arg(format!("/OUT:{}", output.display()))
        .arg(object)
        // Cranelift writes no default-library directives into the object, so
        // the C runtime `main` starts from is named here.
        .arg("libcmt.lib")
        .arg("libucrt.lib")
        .arg("libvcruntime.lib")
        .arg("kernel32.lib");
    Ok(command)
}

#[cfg(not(windows))]
fn linker(object: &Path, output: &Path) -> Result<Command, LinkError> {
    let driver = std::env::var("CC").unwrap_or_else(|_| "cc".to_owned());
    let mut command = Command::new(driver);
    command.arg("-o").arg(output).arg(object).arg("-lm");
    Ok(command)
}
