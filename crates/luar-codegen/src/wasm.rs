//! LIR to WebAssembly.

use std::collections::HashMap;

use luar_lir::inst::{Const, InstKind, Terminator};
use luar_lir::program::{Function as LirFunction, Program};
use luar_lir::ty::{FloatTy, IntTy, Ty};
use wasm_encoder::{
    CodeSection, ExportKind, ExportSection, Function, FunctionSection, Instruction, Module,
    TypeSection, ValType,
};

use crate::Gap;

/// An emitted WebAssembly module.
#[derive(Debug)]
pub struct Wasm {
    pub bytes: Vec<u8>,
    pub gaps: Vec<Gap>,
}

/// Emits the scalar part of `program` as a WebAssembly module (LR4.3, LR47).
#[must_use]
pub fn compile_wasm(program: &Program) -> Wasm {
    let mut module = Module::new();
    let mut types = TypeSection::new();
    let mut functions = FunctionSection::new();
    let mut exports = ExportSection::new();
    let mut code = CodeSection::new();
    let mut gaps = Vec::new();
    let mut emitted = HashMap::new();

    for (id, function) in program.functions() {
        if function.is_template() {
            continue;
        }
        if function.external.is_some() {
            gap(&mut gaps, function, "a WebAssembly function import");
            continue;
        }
        let Some(params) = function
            .params
            .iter()
            .map(value_type)
            .collect::<Option<Vec<_>>>()
        else {
            gap(&mut gaps, function, "a WebAssembly function signature");
            continue;
        };
        let Some(result) = value_type(&function.result) else {
            gap(&mut gaps, function, "a WebAssembly function signature");
            continue;
        };

        let index = u32::try_from(emitted.len()).expect("function count fits in u32");
        let type_index = index;
        types.ty().function(params.iter().copied(), [result]);
        functions.function(type_index);
        emitted.insert(id, index);
    }

    for (id, function) in program.functions() {
        if !emitted.contains_key(&id) {
            continue;
        }
        code.function(&emit_function(function, &emitted, &mut gaps));
    }

    if let Some(entry) = program.entry
        && let Some(index) = emitted.get(&entry)
    {
        exports.export("main", ExportKind::Func, *index);
    }
    for initializer in &program.initializers {
        gap(
            &mut gaps,
            program.function(*initializer),
            "WebAssembly module initialization",
        );
    }

    module.section(&types);
    module.section(&functions);
    if !exports.is_empty() {
        module.section(&exports);
    }
    module.section(&code);

    Wasm {
        bytes: module.finish(),
        gaps,
    }
}

fn emit_function(
    function: &LirFunction,
    functions: &HashMap<luar_lir::program::FuncId, u32>,
    gaps: &mut Vec<Gap>,
) -> Function {
    let mut locals = Vec::new();
    let mut values = HashMap::new();
    let entry = function.block(function.entry);
    for (index, value) in entry.params.iter().enumerate() {
        values.insert(
            *value,
            u32::try_from(index).expect("parameter count fits in u32"),
        );
    }
    for (value, ty) in function.values() {
        if values.contains_key(&value) {
            continue;
        }
        let Some(ty) = value_type(ty) else {
            gap(
                gaps,
                function,
                &format!("a WebAssembly value of type `{ty}`"),
            );
            let mut body = Function::new(Vec::new());
            body.instruction(&Instruction::Unreachable);
            body.instruction(&Instruction::End);
            return body;
        };
        let index = u32::try_from(values.len()).expect("local count fits in u32");
        values.insert(value, index);
        locals.push((1, ty));
    }

    let mut body = Function::new(locals);
    if function.blocks().count() != 1 {
        gap(gaps, function, "WebAssembly control flow");
        body.instruction(&Instruction::Unreachable);
        body.instruction(&Instruction::End);
        return body;
    }

    for inst in &entry.insts {
        match (&inst.kind, inst.result) {
            (InstKind::Const(value), Some(result)) => {
                emit_const(&mut body, value, function.type_of(result));
                body.instruction(&Instruction::LocalSet(values[&result]));
            }
            (
                InstKind::Call {
                    callee,
                    type_args,
                    args,
                },
                Some(result),
            ) if type_args.is_empty() && functions.contains_key(callee) => {
                for argument in args {
                    body.instruction(&Instruction::LocalGet(values[argument]));
                }
                body.instruction(&Instruction::Call(functions[callee]));
                body.instruction(&Instruction::LocalSet(values[&result]));
            }
            (kind, _) => {
                gaps.push(Gap {
                    function: function.name.clone(),
                    span: inst.span,
                    what: format!("WebAssembly lowering for `{kind:?}`"),
                });
            }
        }
    }

    match entry.term.as_ref() {
        Some(Terminator::Return(value)) => {
            body.instruction(&Instruction::LocalGet(values[value]));
        }
        Some(Terminator::Trap(_)) => {
            body.instruction(&Instruction::Unreachable);
        }
        Some(_) => {
            gap(gaps, function, "WebAssembly control flow");
            body.instruction(&Instruction::Unreachable);
        }
        None => {
            gap(gaps, function, "an unterminated LIR block");
            body.instruction(&Instruction::Unreachable);
        }
    }
    body.instruction(&Instruction::End);
    body
}

fn emit_const(body: &mut Function, value: &Const, ty: &Ty) {
    match value_type(ty) {
        Some(ValType::I32) => {
            let bits = match value {
                Const::Unit | Const::Nil => 0,
                Const::Bool(value) => i32::from(*value),
                Const::Int(value) => *value as i32,
                Const::Char(value) => *value as i32,
                _ => 0,
            };
            body.instruction(&Instruction::I32Const(bits));
        }
        Some(ValType::I64) => {
            let Const::Int(value) = value else {
                unreachable!("an i64 constant is an integer")
            };
            body.instruction(&Instruction::I64Const(*value as i64));
        }
        Some(ValType::F32) => {
            let Const::Float(value) = value else {
                unreachable!("an f32 constant is a float")
            };
            body.instruction(&Instruction::F32Const((*value as f32).into()));
        }
        Some(ValType::F64) => {
            let Const::Float(value) = value else {
                unreachable!("an f64 constant is a float")
            };
            body.instruction(&Instruction::F64Const((*value).into()));
        }
        _ => unreachable!("unsupported constants are reported before emission"),
    }
}

fn value_type(ty: &Ty) -> Option<ValType> {
    match ty {
        Ty::Unit | Ty::Nil | Ty::Never | Ty::Bool | Ty::Char => Some(ValType::I32),
        Ty::Int(IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::U8 | IntTy::U16 | IntTy::U32) => {
            Some(ValType::I32)
        }
        Ty::Int(IntTy::I64 | IntTy::U64) => Some(ValType::I64),
        Ty::Int(IntTy::Isize | IntTy::Usize) | Ty::Pointer { .. } => Some(ValType::I32),
        Ty::Float(FloatTy::F32) => Some(ValType::F32),
        Ty::Float(FloatTy::F64) => Some(ValType::F64),
        _ => None,
    }
}

fn gap(gaps: &mut Vec<Gap>, function: &LirFunction, what: &str) {
    gaps.push(Gap {
        function: function.name.clone(),
        span: function.span,
        what: what.to_owned(),
    });
}
