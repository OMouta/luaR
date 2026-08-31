use luar_diagnostics::SourceMap;

// LR4.3, LR47
#[test]
fn int_is_i64_in_webassembly() {
    let mut sources = SourceMap::new();
    let root = sources.add(
        "main.luar",
        "@noinline\nfunction answer(): int\n    return 42\nend\n\nexport function main(): int\n    return answer()\nend\n",
    );
    let lowered = luar_driver::lower(&mut sources, root).unwrap();
    assert!(lowered.gaps.is_empty());

    let wasm = luar_codegen::compile_wasm(&lowered.program);
    assert!(wasm.gaps.is_empty());
    wasmparser::Validator::new()
        .validate_all(&wasm.bytes)
        .unwrap();

    let mut saw_type = false;
    let mut saw_value = false;
    let mut saw_call = false;
    for payload in wasmparser::Parser::new(0).parse_all(&wasm.bytes) {
        match payload.unwrap() {
            wasmparser::Payload::TypeSection(types) => {
                let ty = types.into_iter_err_on_gc_types().next().unwrap().unwrap();
                saw_type = ty.results() == [wasmparser::ValType::I64];
            }
            wasmparser::Payload::CodeSectionEntry(body) => {
                let mut operators = body.get_operators_reader().unwrap();
                while !operators.eof() {
                    let operator = operators.read().unwrap();
                    if matches!(operator, wasmparser::Operator::I64Const { value: 42 }) {
                        saw_value = true;
                    } else if matches!(operator, wasmparser::Operator::Call { function_index: 0 }) {
                        saw_call = true;
                    }
                }
            }
            _ => {}
        }
    }
    assert!(saw_type);
    assert!(saw_value);
    assert!(saw_call);
}
