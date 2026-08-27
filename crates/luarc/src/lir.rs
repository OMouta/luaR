//! `luarc lir`: print what a program lowers to.
//!
//! There is no backend, so the only way to see whether lowering did the right
//! thing is to read what it produced. The text is for a person and nothing
//! parses it.

use std::fs;
use std::process::ExitCode;

use luar_diagnostics::SourceMap;

pub fn run(args: &[String]) -> ExitCode {
    let Some(path) = args.first() else {
        eprintln!("luarc lir: expected a file");
        return ExitCode::from(2);
    };

    let source = match fs::read_to_string(path) {
        Ok(source) => source,
        Err(e) => {
            eprintln!("luarc lir: {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    let mut sources = SourceMap::new();
    let file = sources.add(path, source);

    let lowered = match luar_driver::lower(&mut sources, file) {
        Ok(lowered) => lowered,
        Err(diagnostics) => {
            eprint!("{}", luar_diagnostics::render_all(&sources, &diagnostics));
            return ExitCode::FAILURE;
        }
    };

    print!("{}", luar_lir::print::program(&lowered.program));

    if !lowered.gaps.is_empty() {
        eprintln!("\n{} not lowered:", lowered.gaps.len());
        for gap in &lowered.gaps {
            let file = sources.file(gap.span.file);
            let at = file.position(gap.span.start);
            eprintln!("  {}:{at}: {}", file.path().display(), gap.what);
        }
        return ExitCode::FAILURE;
    }

    ExitCode::SUCCESS
}
