use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/conformance/testing")
        .join(name)
}

fn run(files: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_luarc"))
        .arg("test")
        .args(files.iter().map(|name| fixture(name)))
        .output()
        .unwrap()
}

#[test]
fn sync_and_async_tests_run_in_declaration_order() {
    // LR61, LR78, LR27, LR27.2, LR26.
    let output = run(&["passing.luar"]);
    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8(output.stdout)
        .unwrap()
        .replace("\r\n", "\n");
    let path = fixture("passing.luar");
    assert_eq!(
        stdout,
        format!(
            "init\nfirst\nPASS {}:first\ninit\nchild\ncleanup\nsecond\nPASS {}:second\n2 passed, 0 failed\n",
            path.display(),
            path.display()
        )
    );
}

#[test]
fn failures_do_not_stop_later_tests_or_files() {
    // LR61, LR25.3, LR25.4, LR27.2, LR49, LR70.
    let output = run(&["failing.luar", "passing.luar"]);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    let failed = fixture("failing.luar");
    let passed = fixture("passing.luar");
    let results: Vec<_> = stdout
        .lines()
        .filter(|line| line.starts_with("PASS ") || line.starts_with("FAIL "))
        .collect();
    let expected: Vec<_> = ["assertion", "exception", "panics", "bounds", "asynchronous"]
        .into_iter()
        .map(|name| format!("FAIL {}:{name}", failed.display()))
        .chain([
            format!("PASS {}:last", failed.display()),
            format!("PASS {}:first", passed.display()),
            format!("PASS {}:second", passed.display()),
        ])
        .collect();
    assert_eq!(results, expected);
    for marker in [
        "assertion entered",
        "exception entered",
        "panic entered",
        "bounds entered",
        "child entered",
    ] {
        assert!(stdout.lines().any(|line| line == marker), "{stdout}");
    }
    assert!(stdout.contains("still runs"), "{stdout}");
    assert_eq!(stdout.lines().last(), Some("3 passed, 5 failed"));
}

#[test]
fn no_tests_does_not_call_main() {
    // LR61.
    let output = run(&["no-tests.luar"]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        "0 passed, 0 failed"
    );
}

#[test]
fn rejected_files_fail_without_preventing_later_files() {
    // LR61, LR80.
    let output = run(&["parameters.luar", "passing.luar"]);
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("[LR0227]"), "{stderr}");
    assert!(stderr.contains(":5:1"), "{stderr}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!(stdout.lines().last(), Some("2 passed, 0 failed"));
}

#[test]
fn missing_input_fails() {
    // LR61.
    assert_eq!(run(&[]).status.code(), Some(2));
    assert_eq!(run(&["missing.luar"]).status.code(), Some(1));
}
