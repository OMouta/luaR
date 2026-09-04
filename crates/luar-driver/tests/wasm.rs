use luar_diagnostics::SourceMap;

// LR4.3, LR47
#[test]
fn int_is_i64_in_webassembly() {
    let mut sources = SourceMap::new();
    let root = sources.add(
        "main.luar",
        "@noinline\nfunction answer(): int\n    return 42\nend\n\n@noinline\nfunction less(left: int, right: int): bool\n    return left < right\nend\n\n@noinline\nfunction invert(value: bool): bool\n    return not value\nend\n\nexport function main(): int\n    return answer()\nend\n",
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
    let mut saw_comparison = false;
    let mut saw_not = false;
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
                    } else if matches!(operator, wasmparser::Operator::I64LtS) {
                        saw_comparison = true;
                    } else if matches!(operator, wasmparser::Operator::I32Eqz) {
                        saw_not = true;
                    }
                }
            }
            _ => {}
        }
    }
    assert!(saw_type);
    assert!(saw_value);
    assert!(saw_call);
    assert!(saw_comparison);
    assert!(saw_not);
}

// LR11.1, LR11.5, LR47
#[test]
fn scalar_binary_operations_lower_to_webassembly() {
    let mut sources = SourceMap::new();
    let root = sources.add(
        "main.luar",
        "@noinline\nfunction bitwise(left: i64, right: i64): i64\n    return (left & right) | (left ^ right) << right >> right\nend\n\n@noinline\nfunction signedDivision(left: i64, right: i64): i64\n    return left // right\nend\n\n@noinline\nfunction unsignedDivision(left: u32, right: u32): u32\n    return left // right\nend\n\n@noinline\nfunction arithmetic(left: f64, right: f64): f64\n    return (left + right) * (left - right) / right\nend\n\nexport function main(): i64\n    return bitwise(6, 2)\nend\n",
    );
    let lowered = luar_driver::lower(&mut sources, root).unwrap();
    assert!(lowered.gaps.is_empty());

    let wasm = luar_codegen::compile_wasm(&lowered.program);
    assert!(wasm.gaps.is_empty());
    wasmparser::Validator::new()
        .validate_all(&wasm.bytes)
        .unwrap();

    let mut operators = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(&wasm.bytes) {
        if let wasmparser::Payload::CodeSectionEntry(body) = payload.unwrap() {
            let mut reader = body.get_operators_reader().unwrap();
            while !reader.eof() {
                operators.push(reader.read().unwrap());
            }
        }
    }
    assert!(
        operators
            .iter()
            .any(|op| matches!(op, wasmparser::Operator::I64And))
    );
    assert!(
        operators
            .iter()
            .any(|op| matches!(op, wasmparser::Operator::I64Or))
    );
    assert!(
        operators
            .iter()
            .any(|op| matches!(op, wasmparser::Operator::I64Xor))
    );
    assert!(
        operators
            .iter()
            .any(|op| matches!(op, wasmparser::Operator::I64Shl))
    );
    assert!(
        operators
            .iter()
            .any(|op| matches!(op, wasmparser::Operator::I64ShrS))
    );
    assert!(
        operators
            .iter()
            .any(|op| matches!(op, wasmparser::Operator::I64DivS))
    );
    assert!(
        operators
            .iter()
            .any(|op| matches!(op, wasmparser::Operator::I32DivU))
    );
    assert!(
        operators
            .iter()
            .any(|op| matches!(op, wasmparser::Operator::F64Add))
    );
    assert!(
        operators
            .iter()
            .any(|op| matches!(op, wasmparser::Operator::F64Sub))
    );
    assert!(
        operators
            .iter()
            .any(|op| matches!(op, wasmparser::Operator::F64Mul))
    );
    assert!(
        operators
            .iter()
            .any(|op| matches!(op, wasmparser::Operator::F64Div))
    );
}
