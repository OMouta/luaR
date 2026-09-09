use std::fs;
use std::path::Path;
use std::process::Command;

#[test]
fn format_checks_and_writes_files() {
    // LR64.
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/conformance/formatting");
    let path = std::env::temp_dir().join(format!("luarc-format-{}.luar", std::process::id()));
    let source = fs::read(root.join("blocks.luar")).unwrap();
    fs::write(&path, &source).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_luarc"))
        .args(["fmt", "--check"])
        .arg(&path)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(fs::read(&path).unwrap(), source);

    for args in [vec!["fmt"], vec!["fmt", "--check"]] {
        let output = Command::new(env!("CARGO_BIN_EXE_luarc"))
            .args(args)
            .arg(&path)
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
    }
    let expected = fs::read_to_string(root.join("blocks.formatted"))
        .unwrap()
        .replace("\r\n", "\n");
    assert_eq!(fs::read_to_string(&path).unwrap(), expected);
    fs::remove_file(path).unwrap();
}

#[test]
fn format_preserves_rejected_files() {
    // LR64, LR89.2, LR80.
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/conformance/syntax/an-unclosed-delimiter.luar");
    let path = std::env::temp_dir().join(format!("luarc-format-error-{}.luar", std::process::id()));
    let source = fs::read(fixture).unwrap();
    fs::write(&path, &source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_luarc"))
        .arg("fmt")
        .arg(&path)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("[LR0124]"), "{stderr}");
    assert!(stderr.contains(":7:10"), "{stderr}");
    assert_eq!(fs::read(&path).unwrap(), source);
    fs::remove_file(path).unwrap();
}
