use std::path::Path;
use std::process::Command;

#[test]
fn doc_writes_markdown() {
    // LR62, LR63.
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/conformance/documentation/decorators.luar");
    let output = Command::new(env!("CARGO_BIN_EXE_luarc"))
        .arg("doc")
        .arg(fixture)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8(output.stdout)
            .unwrap()
            .replace("\r\n", "\n"),
        "## `answer`\n\nBefore.\nBetween.\nAfter.\n\n"
    );
}

#[test]
fn run_forwards_arguments_and_exit_status() {
    // LR45.
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/arguments.luar");
    let output = Command::new(env!("CARGO_BIN_EXE_luarc"))
        .arg("run")
        .arg(fixture)
        .args(["two words", "", "a\"quote", "--flag"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(7), "{output:?}");
    assert_eq!(
        String::from_utf8(output.stdout)
            .unwrap()
            .replace("\r\n", "\n"),
        "arguments received\n"
    );
}
