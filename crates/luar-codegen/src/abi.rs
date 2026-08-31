//! Native C argument and result shapes for `@repr("C")` values.

use cranelift_codegen::ir::{AbiParam, ArgumentPurpose, Signature, Type, types};
use cranelift_codegen::isa::CallConv;
use luar_lir::program::{Function, Program};
use luar_lir::ty::{FloatTy, Ty};
use target_lexicon::Architecture;

use crate::layout;
use crate::ty::machine;

#[derive(Clone, Copy)]
pub(crate) struct Part {
    pub offset: i32,
    pub ty: Type,
}

#[derive(Clone)]
pub(crate) enum Param {
    Scalar,
    Direct(Vec<Part>),
    Indirect,
    Stack(u32),
}

#[derive(Clone)]
pub(crate) enum Result {
    Unit,
    Scalar,
    Direct(Vec<Part>),
    Indirect,
}

#[derive(Clone)]
pub(crate) struct CAbi {
    pub signature: Signature,
    pub params: Vec<Param>,
    pub result: Result,
}

#[derive(Clone, Copy)]
pub(crate) enum Target {
    X64Windows,
    X64SystemV,
    Aarch64,
    Aarch64Apple,
}

impl Target {
    pub fn new(architecture: Architecture, call_conv: CallConv) -> Option<Self> {
        match (architecture, call_conv) {
            (Architecture::X86_64 | Architecture::X86_64h, CallConv::WindowsFastcall) => {
                Some(Self::X64Windows)
            }
            (Architecture::X86_64 | Architecture::X86_64h, CallConv::SystemV) => {
                Some(Self::X64SystemV)
            }
            (Architecture::Aarch64(_), CallConv::SystemV | CallConv::WindowsFastcall) => {
                Some(Self::Aarch64)
            }
            (Architecture::Aarch64(_), CallConv::AppleAarch64) => Some(Self::Aarch64Apple),
            _ => None,
        }
    }
}

#[derive(Default)]
struct Registers {
    integer: usize,
    float: usize,
}

impl CAbi {
    pub fn new(
        program: &Program,
        function: &Function,
        pointer: Type,
        call_conv: CallConv,
        target: Target,
    ) -> Option<Self> {
        let result = classify_result(program, &function.result, pointer, target)?;
        let mut registers = Registers::default();
        if matches!(result, Result::Indirect)
            && matches!(target, Target::X64Windows | Target::X64SystemV)
        {
            registers.integer = 1;
        }

        let mut params = Vec::with_capacity(function.params.len());
        for ty in &function.params {
            params.push(classify_param(
                program,
                ty,
                pointer,
                target,
                &mut registers,
            )?);
        }

        let mut signature = Signature::new(call_conv);
        if matches!(result, Result::Indirect) {
            signature
                .params
                .push(AbiParam::special(pointer, ArgumentPurpose::StructReturn));
        }
        for (ty, param) in function.params.iter().zip(&params) {
            match param {
                Param::Scalar => signature.params.push(AbiParam::new(machine(ty, pointer)?)),
                Param::Direct(parts) => signature
                    .params
                    .extend(parts.iter().map(|part| AbiParam::new(part.ty))),
                Param::Indirect => signature.params.push(AbiParam::new(pointer)),
                Param::Stack(size) => signature.params.push(AbiParam::special(
                    pointer,
                    ArgumentPurpose::StructArgument(*size),
                )),
            }
        }
        match &result {
            Result::Unit | Result::Indirect => {}
            Result::Scalar => signature
                .returns
                .push(AbiParam::new(machine(&function.result, pointer)?)),
            Result::Direct(parts) => signature
                .returns
                .extend(parts.iter().map(|part| AbiParam::new(part.ty))),
        }

        Some(Self {
            signature,
            params,
            result,
        })
    }
}

fn classify_result(program: &Program, ty: &Ty, pointer: Type, target: Target) -> Option<Result> {
    if *ty == Ty::Unit {
        return Some(Result::Unit);
    }
    if !layout::is_aggregate(ty) {
        machine(ty, pointer)?;
        return Some(Result::Scalar);
    }
    if !layout::is_repr_c(program, ty) {
        return None;
    }

    let size = layout::abi_size(program, ty, pointer)?;
    match target {
        Target::X64Windows => match size {
            1 | 2 | 4 | 8 => Some(Result::Direct(vec![Part {
                offset: 0,
                ty: integer_part(size),
            }])),
            _ => Some(Result::Indirect),
        },
        Target::X64SystemV => {
            let parts = system_v_parts(program, ty, pointer)?;
            parts.map_or(Some(Result::Indirect), |parts| Some(Result::Direct(parts)))
        }
        Target::Aarch64 | Target::Aarch64Apple => {
            if let Some(parts) = homogeneous_float_parts(program, ty, pointer) {
                return Some(Result::Direct(parts));
            }
            if size <= 16 {
                Some(Result::Direct(integer_parts(size)))
            } else {
                Some(Result::Indirect)
            }
        }
    }
}

fn classify_param(
    program: &Program,
    ty: &Ty,
    pointer: Type,
    target: Target,
    registers: &mut Registers,
) -> Option<Param> {
    if !layout::is_aggregate(ty) {
        let machine = machine(ty, pointer)?;
        match target {
            Target::X64SystemV | Target::Aarch64 | Target::Aarch64Apple if machine.is_float() => {
                registers.float = (registers.float + 1).min(8);
            }
            Target::X64SystemV => registers.integer = (registers.integer + 1).min(6),
            Target::Aarch64 | Target::Aarch64Apple => {
                registers.integer = (registers.integer + 1).min(8);
            }
            Target::X64Windows => {}
        }
        return Some(Param::Scalar);
    }
    if !layout::is_repr_c(program, ty) {
        return None;
    }

    let size = layout::abi_size(program, ty, pointer)?;
    match target {
        Target::X64Windows => match size {
            1 | 2 | 4 | 8 => Some(Param::Direct(vec![Part {
                offset: 0,
                ty: integer_part(size),
            }])),
            _ => Some(Param::Indirect),
        },
        Target::X64SystemV => {
            let Some(parts) = system_v_parts(program, ty, pointer)? else {
                return Some(Param::Stack(stack_size(size)?));
            };
            let integer = parts.iter().filter(|part| !part.ty.is_float()).count();
            let float = parts.len() - integer;
            if registers.integer + integer <= 6 && registers.float + float <= 8 {
                registers.integer += integer;
                registers.float += float;
                Some(Param::Direct(parts))
            } else {
                Some(Param::Stack(stack_size(size)?))
            }
        }
        Target::Aarch64 | Target::Aarch64Apple => {
            if let Some(parts) = homogeneous_float_parts(program, ty, pointer) {
                let remaining = 8_usize.saturating_sub(registers.float);
                if remaining >= parts.len() {
                    registers.float += parts.len();
                    return Some(Param::Direct(parts));
                }
                if remaining == 0 {
                    return Some(Param::Direct(parts));
                }
                return None;
            }
            if size <= 16 {
                let parts = integer_parts(size);
                registers.integer = (registers.integer + parts.len()).min(8);
                Some(Param::Direct(parts))
            } else {
                registers.integer = (registers.integer + 1).min(8);
                Some(Param::Indirect)
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SystemVClass {
    Empty,
    Integer,
    Sse,
}

fn system_v_parts(program: &Program, ty: &Ty, pointer: Type) -> Option<Option<Vec<Part>>> {
    let size = layout::abi_size(program, ty, pointer)?;
    if size > 16 {
        return Some(None);
    }
    let mut classes = vec![SystemVClass::Empty; usize::try_from((size + 7) / 8).ok()?];
    classify_system_v(program, ty, pointer, 0, &mut classes)?;
    let mut parts = Vec::with_capacity(classes.len());
    for (index, class) in classes.into_iter().enumerate() {
        let offset = i32::try_from(index).ok()?.checked_mul(8)?;
        let bytes = (size - offset).min(8);
        let ty = match class {
            SystemVClass::Integer => integer_part(bytes),
            SystemVClass::Sse if bytes <= 4 => types::F32,
            SystemVClass::Sse => types::F64,
            SystemVClass::Empty => return None,
        };
        parts.push(Part { offset, ty });
    }
    Some(Some(parts))
}

fn classify_system_v(
    program: &Program,
    ty: &Ty,
    pointer: Type,
    base: i32,
    classes: &mut [SystemVClass],
) -> Option<()> {
    let class = match ty {
        Ty::Float(_) => Some(SystemVClass::Sse),
        Ty::Bool | Ty::Int(_) | Ty::Pointer { .. } | Ty::Char => Some(SystemVClass::Integer),
        Ty::Named { .. } if layout::is_repr_c(program, ty) => None,
        _ => return None,
    };
    if let Some(class) = class {
        let size = layout::abi_size(program, ty, pointer)?;
        let first = usize::try_from(base / 8).ok()?;
        let last = usize::try_from((base + size - 1) / 8).ok()?;
        for held in classes.get_mut(first..=last)? {
            *held = merge(*held, class);
        }
        return Some(());
    }

    for (index, part) in layout::parts(program, ty)?.iter().enumerate() {
        let index = u32::try_from(index).ok()?;
        let offset = layout::field_offset(program, ty, index, pointer)?;
        classify_system_v(program, part, pointer, base.checked_add(offset)?, classes)?;
    }
    Some(())
}

fn merge(left: SystemVClass, right: SystemVClass) -> SystemVClass {
    match (left, right) {
        (SystemVClass::Empty, other) => other,
        (other, SystemVClass::Empty) => other,
        (SystemVClass::Integer, _) | (_, SystemVClass::Integer) => SystemVClass::Integer,
        _ => SystemVClass::Sse,
    }
}

fn homogeneous_float_parts(program: &Program, ty: &Ty, pointer: Type) -> Option<Vec<Part>> {
    let mut parts = Vec::new();
    flatten_floats(program, ty, pointer, 0, &mut parts)?;
    if parts.is_empty() || parts.len() > 4 || parts.iter().any(|part| part.ty != parts[0].ty) {
        return None;
    }
    Some(parts)
}

fn flatten_floats(
    program: &Program,
    ty: &Ty,
    pointer: Type,
    base: i32,
    parts: &mut Vec<Part>,
) -> Option<()> {
    match ty {
        Ty::Float(FloatTy::F32) => parts.push(Part {
            offset: base,
            ty: types::F32,
        }),
        Ty::Float(FloatTy::F64) => parts.push(Part {
            offset: base,
            ty: types::F64,
        }),
        Ty::Named { .. } if layout::is_repr_c(program, ty) => {
            for (index, part) in layout::parts(program, ty)?.iter().enumerate() {
                let index = u32::try_from(index).ok()?;
                let offset = layout::field_offset(program, ty, index, pointer)?;
                flatten_floats(program, part, pointer, base.checked_add(offset)?, parts)?;
            }
        }
        _ => return None,
    }
    Some(())
}

fn integer_parts(size: i32) -> Vec<Part> {
    let mut parts = Vec::new();
    let mut offset = 0;
    while offset < size {
        let bytes = (size - offset).min(8);
        parts.push(Part {
            offset,
            ty: integer_part(bytes),
        });
        offset += 8;
    }
    parts
}

fn integer_part(bytes: i32) -> Type {
    match bytes {
        1 => types::I8,
        2 => types::I16,
        3 | 4 => types::I32,
        _ => types::I64,
    }
}

fn stack_size(size: i32) -> Option<u32> {
    u32::try_from(size.checked_add(7)? / 8 * 8).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use luar_diagnostics::{FileId, Span};
    use luar_lir::program::{Field, Nominal, Shape, Struct};
    use luar_lir::ty::IntTy;

    const SPAN: Span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };

    fn structure(program: &mut Program, name: &str, fields: Vec<Ty>) -> Ty {
        let id = program.add_type(Nominal {
            name: name.to_owned(),
            type_params: Vec::new(),
            shape: Shape::Struct(Struct {
                fields: fields
                    .into_iter()
                    .enumerate()
                    .map(|(index, ty)| Field {
                        name: index.to_string(),
                        ty,
                    })
                    .collect(),
                reference: false,
                repr_c: true,
            }),
            span: SPAN,
        });
        Ty::Named {
            id,
            args: Vec::new(),
        }
    }

    fn function(params: Vec<Ty>, result: Ty) -> Function {
        Function::new("native".to_owned(), params, result, SPAN)
    }

    #[test]
    fn windows_x64_passes_only_word_sized_structs_in_registers() {
        let mut program = Program::default();
        let pair = structure(
            &mut program,
            "Pair",
            vec![Ty::Int(IntTy::I32), Ty::Int(IntTy::I32)],
        );
        let complex = structure(
            &mut program,
            "Complex",
            vec![Ty::Float(FloatTy::F64), Ty::Float(FloatTy::F64)],
        );
        let function = function(vec![pair.clone(), complex], pair);
        let abi = CAbi::new(
            &program,
            &function,
            types::I64,
            CallConv::WindowsFastcall,
            Target::X64Windows,
        )
        .unwrap();

        assert!(
            matches!(&abi.params[0], Param::Direct(parts) if parts.len() == 1 && parts[0].ty == types::I64)
        );
        assert!(matches!(&abi.params[1], Param::Indirect));
        assert!(
            matches!(&abi.result, Result::Direct(parts) if parts.len() == 1 && parts[0].ty == types::I64)
        );
    }

    #[test]
    fn system_v_spills_a_whole_struct_when_integer_registers_are_full() {
        let mut program = Program::default();
        let mixed = structure(
            &mut program,
            "Mixed",
            vec![Ty::Float(FloatTy::F64), Ty::Int(IntTy::I32)],
        );
        let mut params = vec![Ty::Int(IntTy::I64); 6];
        params.push(mixed);
        let function = function(params, Ty::Unit);
        let abi = CAbi::new(
            &program,
            &function,
            types::I64,
            CallConv::SystemV,
            Target::X64SystemV,
        )
        .unwrap();

        assert!(matches!(&abi.params[6], Param::Stack(16)));
    }

    #[test]
    fn aarch64_uses_float_parts_for_homogeneous_aggregates() {
        let mut program = Program::default();
        let complex = structure(
            &mut program,
            "Complex",
            vec![Ty::Float(FloatTy::F64), Ty::Float(FloatTy::F64)],
        );
        let function = function(vec![complex.clone()], complex);
        let abi = CAbi::new(
            &program,
            &function,
            types::I64,
            CallConv::SystemV,
            Target::Aarch64,
        )
        .unwrap();

        assert!(
            matches!(&abi.params[0], Param::Direct(parts) if parts.len() == 2 && parts.iter().all(|part| part.ty == types::F64))
        );
        assert!(
            matches!(&abi.result, Result::Direct(parts) if parts.len() == 2 && parts.iter().all(|part| part.ty == types::F64))
        );
    }

    #[test]
    fn aarch64_passes_an_hfa_on_the_stack_after_full_float_registers() {
        let mut program = Program::default();
        let pair = structure(
            &mut program,
            "Pair",
            vec![Ty::Float(FloatTy::F32), Ty::Float(FloatTy::F32)],
        );
        let mut params = vec![Ty::Float(FloatTy::F64); 8];
        params.push(pair);
        let function = function(params, Ty::Unit);

        for (call_conv, target) in [
            (CallConv::SystemV, Target::Aarch64),
            (CallConv::AppleAarch64, Target::Aarch64Apple),
        ] {
            let abi = CAbi::new(&program, &function, types::I64, call_conv, target).unwrap();
            assert!(
                matches!(&abi.params[8], Param::Direct(parts) if parts.len() == 2 && parts.iter().all(|part| part.ty == types::F32))
            );
        }
    }
}
