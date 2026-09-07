use std::path::Path;
use std::process::Command;

#[test]
fn task_runner_reports_help_and_unknown_commands() {
    // LR45.
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    for (arguments, code, expected) in [
        (vec![], 2, "usage:"),
        (vec!["help"], 0, "usage:"),
        (vec!["unknown-task"], 2, "is not a command"),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_luarc"))
            .current_dir(&root)
            .args(["run", "luar.luar"])
            .args(arguments)
            .output()
            .unwrap();

        assert_eq!(output.status.code(), Some(code), "{output:?}");
        assert!(String::from_utf8(output.stdout).unwrap().contains(expected));
    }
}
