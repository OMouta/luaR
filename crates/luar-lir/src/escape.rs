//! Escape analysis for value structs (LR29).

use std::collections::HashSet;

use crate::inst::{Allocation, InstKind, Terminator, Value};
use crate::program::{FuncId, Function, Program, Shape};
use crate::ty::{Ty, TypeId};

pub fn run(program: &mut Program) {
    let values: HashSet<TypeId> = program
        .types()
        .filter_map(|(id, nominal)| match &nominal.shape {
            Shape::Struct(structure) if !structure.reference => Some(id),
            _ => None,
        })
        .collect();
    let functions: Vec<FuncId> = program.functions().map(|(id, _)| id).collect();

    for id in functions {
        place(program.function_mut(id), &values);
    }
}

fn place(function: &mut Function, value_structs: &HashSet<TypeId>) {
    let candidates: Vec<(Value, bool)> = function
        .blocks()
        .flat_map(|(_, block)| &block.insts)
        .filter_map(|inst| {
            let result = inst.result?;
            if !is_value_struct(function.type_of(result), value_structs) {
                return None;
            }
            match inst.kind {
                InstKind::MakeStruct { .. } => Some((result, true)),
                InstKind::CopyValue { .. } => Some((result, false)),
                _ => None,
            }
        })
        .collect();

    for (value, literal) in candidates {
        let allocation = allocation(function, value, literal);
        for block in function.blocks_mut() {
            let Some(inst) = block
                .insts
                .iter_mut()
                .find(|inst| inst.result == Some(value))
            else {
                continue;
            };
            match &mut inst.kind {
                InstKind::MakeStruct {
                    allocation: held, ..
                }
                | InstKind::CopyValue {
                    allocation: held, ..
                } => *held = allocation,
                _ => {}
            }
            break;
        }
    }
}

fn is_value_struct(ty: &Ty, values: &HashSet<TypeId>) -> bool {
    matches!(ty, Ty::Named { id, .. } if values.contains(id))
}

fn allocation(function: &Function, value: Value, literal: bool) -> Allocation {
    let mut writable = !literal;

    for (_, block) in function.blocks() {
        for inst in &block.insts {
            if !uses(&inst.kind, value) {
                continue;
            }
            match inst.kind {
                InstKind::GetField { object, .. } if object == value => {}
                InstKind::SetField {
                    object,
                    value: written,
                    ..
                } if object == value && written != value => writable = true,
                InstKind::CopyValue { value: source, .. } if source == value => writable = true,
                _ => return Allocation::Managed,
            }
        }
        if block
            .term
            .as_ref()
            .is_some_and(|term| terminator_uses(term, value))
        {
            return Allocation::Managed;
        }
    }

    if writable {
        Allocation::Stack
    } else {
        Allocation::Registers
    }
}

fn terminator_uses(term: &Terminator, value: Value) -> bool {
    match term {
        Terminator::Jump(target) => target.args.contains(&value),
        Terminator::Branch {
            condition,
            then,
            otherwise,
        } => *condition == value || then.args.contains(&value) || otherwise.args.contains(&value),
        Terminator::Switch {
            value: held,
            cases,
            default,
        } => {
            *held == value
                || cases.iter().any(|(_, target)| target.args.contains(&value))
                || default.args.contains(&value)
        }
        Terminator::Return(held) => *held == value,
        Terminator::Trap(_) => false,
    }
}
fn uses(inst: &InstKind, value: Value) -> bool {
    inst.operands().contains(&value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inst::{Const, Inst};
    use crate::program::{Field, Nominal, Struct};
    use luar_diagnostics::{FileId, Span};

    const SPAN: Span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };

    #[test]
    fn read_only_literal_uses_registers() {
        let (mut program, function, value) = fixture(false);
        read(&mut program, function, value);
        finish(&mut program, function);
        run(&mut program);
        assert_eq!(placed(&program, function, value), Allocation::Registers);
    }

    #[test]
    fn mutable_literal_uses_the_stack() {
        let (mut program, function, value) = fixture(false);
        let one = constant(&mut program, function);
        program
            .function_mut(function)
            .block_mut(crate::program::BlockId(0))
            .insts
            .push(Inst {
                result: None,
                kind: InstKind::SetField {
                    object: value,
                    field: 0,
                    value: one,
                },
                span: SPAN,
            });
        finish(&mut program, function);
        run(&mut program);
        assert_eq!(placed(&program, function, value), Allocation::Stack);
    }

    #[test]
    fn returned_literal_stays_managed() {
        let (mut program, function, value) = fixture(false);
        program
            .function_mut(function)
            .block_mut(crate::program::BlockId(0))
            .term = Some(Terminator::Return(value));
        run(&mut program);
        assert_eq!(placed(&program, function, value), Allocation::Managed);
    }

    #[test]
    fn local_copy_and_its_source_use_the_stack() {
        let (mut program, function, value) = fixture(false);
        let ty = program.function(function).type_of(value).clone();
        let copied = {
            let function = program.function_mut(function);
            let copied = function.add_value(ty);
            function.block_mut(function.entry).insts.push(Inst {
                result: Some(copied),
                kind: InstKind::CopyValue {
                    value,
                    allocation: Allocation::Managed,
                },
                span: SPAN,
            });
            copied
        };
        read(&mut program, function, copied);
        finish(&mut program, function);
        run(&mut program);
        assert_eq!(placed(&program, function, value), Allocation::Stack);
        assert_eq!(placed(&program, function, copied), Allocation::Stack);
    }

    #[test]
    fn reference_struct_stays_managed() {
        let (mut program, function, value) = fixture(true);
        read(&mut program, function, value);
        finish(&mut program, function);
        run(&mut program);
        assert_eq!(placed(&program, function, value), Allocation::Managed);
    }

    fn fixture(reference: bool) -> (Program, FuncId, Value) {
        let mut program = Program::default();
        let id = program.add_type(Nominal {
            name: "Point".to_owned(),
            type_params: Vec::new(),
            shape: Shape::Struct(Struct {
                fields: vec![Field {
                    name: "x".to_owned(),
                    ty: Ty::INT,
                }],
                reference,
                repr_c: false,
            }),
            span: SPAN,
        });
        let ty = Ty::Named {
            id,
            args: Vec::new(),
        };
        let mut function = Function::new("main".to_owned(), Vec::new(), Ty::Unit, SPAN);
        let entry = function.entry;
        let field = function.add_value(Ty::INT);
        function.block_mut(entry).insts.push(Inst {
            result: Some(field),
            kind: InstKind::Const(Const::Int(1)),
            span: SPAN,
        });
        let value = function.add_value(ty.clone());
        function.block_mut(entry).insts.push(Inst {
            result: Some(value),
            kind: InstKind::MakeStruct {
                ty,
                fields: vec![field],
                allocation: Allocation::Managed,
            },
            span: SPAN,
        });
        let id = program.add_function(function);
        (program, id, value)
    }

    fn read(program: &mut Program, function: FuncId, value: Value) {
        let function = program.function_mut(function);
        let read = function.add_value(Ty::INT);
        function.block_mut(function.entry).insts.push(Inst {
            result: Some(read),
            kind: InstKind::GetField {
                object: value,
                field: 0,
            },
            span: SPAN,
        });
    }

    fn constant(program: &mut Program, function: FuncId) -> Value {
        let function = program.function_mut(function);
        let value = function.add_value(Ty::INT);
        function.block_mut(function.entry).insts.push(Inst {
            result: Some(value),
            kind: InstKind::Const(Const::Int(1)),
            span: SPAN,
        });
        value
    }

    fn finish(program: &mut Program, function: FuncId) {
        let function = program.function_mut(function);
        let unit = function.add_value(Ty::Unit);
        function.block_mut(function.entry).insts.push(Inst {
            result: Some(unit),
            kind: InstKind::Const(Const::Unit),
            span: SPAN,
        });
        function.block_mut(function.entry).term = Some(Terminator::Return(unit));
    }

    fn placed(program: &Program, function: FuncId, value: Value) -> Allocation {
        program
            .function(function)
            .blocks()
            .flat_map(|(_, block)| &block.insts)
            .find_map(|inst| {
                (inst.result == Some(value)).then_some(match inst.kind {
                    InstKind::MakeStruct { allocation, .. }
                    | InstKind::CopyValue { allocation, .. } => allocation,
                    _ => Allocation::Managed,
                })
            })
            .expect("the allocation")
    }
}
