//! The LuaR compiler command line.

mod check;
mod lir;
mod test;

use std::process::ExitCode;

const USAGE: &str = "\
luarc — the LuaR compiler

usage:
  luarc check <file>...     read the files and report what is wrong with them
  luarc test [filter]       run the conformance suite, or the tests matching
  luarc coverage            report which spec sections have no test
  luarc run <file>          run a program
  luarc lir <file>          print what a program lowers to

Paths are relative to the working directory.
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (command, rest) = match args.split_first() {
        Some((command, rest)) => (command.as_str(), rest),
        None => {
            eprint!("{USAGE}");
            return ExitCode::from(2);
        }
    };

    match command {
        "check" => check::run(rest),
        "test" => test::run(rest.first().map(String::as_str)),
        "coverage" => test::coverage(),
        "run" => run(rest),
        "lir" => lir::run(rest),
        "help" | "--help" | "-h" => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        other => {
            eprintln!("luarc: `{other}` is not a command\n");
            eprint!("{USAGE}");
            ExitCode::from(2)
        }
    }
}

/// Running a program needs a backend, and there is none yet.
///
/// The command exists so that what is missing is a stated gap rather than an
/// unknown one. Until then `check` says whether a program is one.
fn run(args: &[String]) -> ExitCode {
    if args.is_empty() {
        eprintln!("luarc run: expected a file");
        return ExitCode::from(2);
    }

    let checked = check::run(args);
    if checked != ExitCode::SUCCESS {
        return checked;
    }

    eprintln!("luarc run: the file is a valid program, and there is no backend to run it on yet.");
    ExitCode::from(2)
}
