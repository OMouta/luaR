//! The LuaR compiler command line.

mod check;
mod lir;
mod run;
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
        "run" => run::run(rest),
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
