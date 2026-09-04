//! LIR to WebAssembly.

use std::collections::HashMap;

use luar_lir::inst::{BinaryOp, Const, InstKind, Terminator, UnaryOp};
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
            (InstKind::Unary { op, operand }, Some(result))
                if emit_unary(&mut body, *op, function.type_of(*operand), values[operand]) =>
            {
                body.instruction(&Instruction::LocalSet(values[&result]));
            }
            (InstKind::Convert { value, to }, Some(result))
                if emit_conversion(&mut body, function.type_of(*value), to, values[value]) =>
            {
                body.instruction(&Instruction::LocalSet(values[&result]));
            }
            (InstKind::Binary { op, left, right }, Some(result))
                if emit_comparison(
                    &mut body,
                    *op,
                    function.type_of(*left),
                    values[left],
                    values[right],
                ) =>
            {
                body.instruction(&Instruction::LocalSet(values[&result]));
            }
            (InstKind::Binary { op, left, right }, Some(result))
                if emit_binary(
                    &mut body,
                    *op,
                    function.type_of(*left),
                    values[left],
                    values[right],
                ) =>
            {
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

fn emit_unary(body: &mut Function, op: UnaryOp, ty: &Ty, operand: u32) -> bool {
    let instruction = match (op, value_type(ty)) {
        (UnaryOp::Not, Some(ValType::I32)) => Some(Instruction::I32Eqz),
        (UnaryOp::BitNot, Some(ValType::I32)) => {
            body.instruction(&Instruction::LocalGet(operand));
            body.instruction(&Instruction::I32Const(-1));
            body.instruction(&Instruction::I32Xor);
            return true;
        }
        (UnaryOp::BitNot, Some(ValType::I64)) => {
            body.instruction(&Instruction::LocalGet(operand));
            body.instruction(&Instruction::I64Const(-1));
            body.instruction(&Instruction::I64Xor);
            return true;
        }
        (UnaryOp::Negate, Some(ValType::F32)) => Some(Instruction::F32Neg),
        (UnaryOp::Negate, Some(ValType::F64)) => Some(Instruction::F64Neg),
        _ => None,
    };
    let Some(instruction) = instruction else {
        return false;
    };
    body.instruction(&Instruction::LocalGet(operand));
    body.instruction(&instruction);
    true
}

fn emit_conversion(body: &mut Function, from: &Ty, to: &Ty, value: u32) -> bool {
    let instruction = match (from, to) {
        (Ty::Float(FloatTy::F32), Ty::Float(FloatTy::F64)) => Instruction::F64PromoteF32,
        (Ty::Float(FloatTy::F64), Ty::Float(FloatTy::F32)) => Instruction::F32DemoteF64,
        (Ty::Int(IntTy::I32), Ty::Int(IntTy::I64)) => Instruction::I64ExtendI32S,
        (Ty::Int(IntTy::U32), Ty::Int(IntTy::U64)) => Instruction::I64ExtendI32U,
        (Ty::Int(IntTy::I32), Ty::Float(FloatTy::F32)) => Instruction::F32ConvertI32S,
        (Ty::Int(IntTy::U32), Ty::Float(FloatTy::F32)) => Instruction::F32ConvertI32U,
        (Ty::Int(IntTy::I64), Ty::Float(FloatTy::F32)) => Instruction::F32ConvertI64S,
        (Ty::Int(IntTy::U64), Ty::Float(FloatTy::F32)) => Instruction::F32ConvertI64U,
        (Ty::Int(IntTy::I32), Ty::Float(FloatTy::F64)) => Instruction::F64ConvertI32S,
        (Ty::Int(IntTy::U32), Ty::Float(FloatTy::F64)) => Instruction::F64ConvertI32U,
        (Ty::Int(IntTy::I64), Ty::Float(FloatTy::F64)) => Instruction::F64ConvertI64S,
        (Ty::Int(IntTy::U64), Ty::Float(FloatTy::F64)) => Instruction::F64ConvertI64U,
        (Ty::Float(FloatTy::F32), Ty::Int(IntTy::I32)) => Instruction::I32TruncF32S,
        (Ty::Float(FloatTy::F32), Ty::Int(IntTy::U32)) => Instruction::I32TruncF32U,
        (Ty::Float(FloatTy::F64), Ty::Int(IntTy::I32)) => Instruction::I32TruncF64S,
        (Ty::Float(FloatTy::F64), Ty::Int(IntTy::U32)) => Instruction::I32TruncF64U,
        (Ty::Float(FloatTy::F32), Ty::Int(IntTy::I64)) => Instruction::I64TruncF32S,
        (Ty::Float(FloatTy::F32), Ty::Int(IntTy::U64)) => Instruction::I64TruncF32U,
        (Ty::Float(FloatTy::F64), Ty::Int(IntTy::I64)) => Instruction::I64TruncF64S,
        (Ty::Float(FloatTy::F64), Ty::Int(IntTy::U64)) => Instruction::I64TruncF64U,
        (Ty::Int(IntTy::I64 | IntTy::U64), Ty::Int(IntTy::I32 | IntTy::U32)) => {
            Instruction::I32WrapI64
        }
        _ if from == to => {
            body.instruction(&Instruction::LocalGet(value));
            return true;
        }
        _ => return false,
    };
    body.instruction(&Instruction::LocalGet(value));
    body.instruction(&instruction);
    true
}

fn emit_comparison(body: &mut Function, op: BinaryOp, ty: &Ty, left: u32, right: u32) -> bool {
    let Some(instruction) = comparison(op, ty) else {
        return false;
    };
    body.instruction(&Instruction::LocalGet(left));
    body.instruction(&Instruction::LocalGet(right));
    body.instruction(&instruction);
    true
}

fn emit_binary(body: &mut Function, op: BinaryOp, ty: &Ty, left: u32, right: u32) -> bool {
    let instruction = match (value_type(ty), op) {
        (Some(ValType::I32), BinaryOp::BitAnd) => Instruction::I32And,
        (Some(ValType::I32), BinaryOp::BitOr) => Instruction::I32Or,
        (Some(ValType::I32), BinaryOp::BitXor) => Instruction::I32Xor,
        (Some(ValType::I32), BinaryOp::ShiftLeft) => Instruction::I32Shl,
        (Some(ValType::I32), BinaryOp::ShiftRight) if is_signed(ty) => Instruction::I32ShrS,
        (Some(ValType::I32), BinaryOp::ShiftRight) => Instruction::I32ShrU,
        (Some(ValType::I32), BinaryOp::IntegerDivide) if is_signed(ty) => Instruction::I32DivS,
        (Some(ValType::I32), BinaryOp::IntegerDivide) => Instruction::I32DivU,
        (Some(ValType::I64), BinaryOp::BitAnd) => Instruction::I64And,
        (Some(ValType::I64), BinaryOp::BitOr) => Instruction::I64Or,
        (Some(ValType::I64), BinaryOp::BitXor) => Instruction::I64Xor,
        (Some(ValType::I64), BinaryOp::ShiftLeft) => Instruction::I64Shl,
        (Some(ValType::I64), BinaryOp::ShiftRight) if is_signed(ty) => Instruction::I64ShrS,
        (Some(ValType::I64), BinaryOp::ShiftRight) => Instruction::I64ShrU,
        (Some(ValType::I64), BinaryOp::IntegerDivide) if is_signed(ty) => Instruction::I64DivS,
        (Some(ValType::I64), BinaryOp::IntegerDivide) => Instruction::I64DivU,
        (Some(ValType::F32), BinaryOp::Add) => Instruction::F32Add,
        (Some(ValType::F32), BinaryOp::Subtract) => Instruction::F32Sub,
        (Some(ValType::F32), BinaryOp::Multiply) => Instruction::F32Mul,
        (Some(ValType::F32), BinaryOp::Divide) => Instruction::F32Div,
        (Some(ValType::F64), BinaryOp::Add) => Instruction::F64Add,
        (Some(ValType::F64), BinaryOp::Subtract) => Instruction::F64Sub,
        (Some(ValType::F64), BinaryOp::Multiply) => Instruction::F64Mul,
        (Some(ValType::F64), BinaryOp::Divide) => Instruction::F64Div,
        _ => return false,
    };
    body.instruction(&Instruction::LocalGet(left));
    body.instruction(&Instruction::LocalGet(right));
    body.instruction(&instruction);
    true
}

fn is_signed(ty: &Ty) -> bool {
    matches!(ty, Ty::Int(int) if int.is_signed())
}

fn comparison(op: BinaryOp, ty: &Ty) -> Option<Instruction<'static>> {
    let signed = is_signed(ty);
    match (value_type(ty)?, op, signed) {
        (ValType::I32, BinaryOp::Equal, _) => Some(Instruction::I32Eq),
        (ValType::I32, BinaryOp::NotEqual, _) => Some(Instruction::I32Ne),
        (ValType::I32, BinaryOp::Less, true) => Some(Instruction::I32LtS),
        (ValType::I32, BinaryOp::Less, false) => Some(Instruction::I32LtU),
        (ValType::I32, BinaryOp::LessEqual, true) => Some(Instruction::I32LeS),
        (ValType::I32, BinaryOp::LessEqual, false) => Some(Instruction::I32LeU),
        (ValType::I32, BinaryOp::Greater, true) => Some(Instruction::I32GtS),
        (ValType::I32, BinaryOp::Greater, false) => Some(Instruction::I32GtU),
        (ValType::I32, BinaryOp::GreaterEqual, true) => Some(Instruction::I32GeS),
        (ValType::I32, BinaryOp::GreaterEqual, false) => Some(Instruction::I32GeU),
        (ValType::I64, BinaryOp::Equal, _) => Some(Instruction::I64Eq),
        (ValType::I64, BinaryOp::NotEqual, _) => Some(Instruction::I64Ne),
        (ValType::I64, BinaryOp::Less, true) => Some(Instruction::I64LtS),
        (ValType::I64, BinaryOp::Less, false) => Some(Instruction::I64LtU),
        (ValType::I64, BinaryOp::LessEqual, true) => Some(Instruction::I64LeS),
        (ValType::I64, BinaryOp::LessEqual, false) => Some(Instruction::I64LeU),
        (ValType::I64, BinaryOp::Greater, true) => Some(Instruction::I64GtS),
        (ValType::I64, BinaryOp::Greater, false) => Some(Instruction::I64GtU),
        (ValType::I64, BinaryOp::GreaterEqual, true) => Some(Instruction::I64GeS),
        (ValType::I64, BinaryOp::GreaterEqual, false) => Some(Instruction::I64GeU),
        (ValType::F32, BinaryOp::Equal, _) => Some(Instruction::F32Eq),
        (ValType::F32, BinaryOp::NotEqual, _) => Some(Instruction::F32Ne),
        (ValType::F32, BinaryOp::Less, _) => Some(Instruction::F32Lt),
        (ValType::F32, BinaryOp::LessEqual, _) => Some(Instruction::F32Le),
        (ValType::F32, BinaryOp::Greater, _) => Some(Instruction::F32Gt),
        (ValType::F32, BinaryOp::GreaterEqual, _) => Some(Instruction::F32Ge),
        (ValType::F64, BinaryOp::Equal, _) => Some(Instruction::F64Eq),
        (ValType::F64, BinaryOp::NotEqual, _) => Some(Instruction::F64Ne),
        (ValType::F64, BinaryOp::Less, _) => Some(Instruction::F64Lt),
        (ValType::F64, BinaryOp::LessEqual, _) => Some(Instruction::F64Le),
        (ValType::F64, BinaryOp::Greater, _) => Some(Instruction::F64Gt),
        (ValType::F64, BinaryOp::GreaterEqual, _) => Some(Instruction::F64Ge),
        _ => None,
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
