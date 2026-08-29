//! Bounds-check elimination (LR70).

use std::collections::HashMap;

use crate::inst::{BinaryOp, Const, Effect, InstKind, Target, Terminator, Value};
use crate::program::{BlockId, FuncId, Function, Program};
use crate::ty::{Builtin, Ty};

pub fn run(program: &mut Program) {
    let functions: Vec<FuncId> = program.functions().map(|(id, _)| id).collect();
    for id in functions {
        eliminate(program.function_mut(id));
    }
}

fn eliminate(function: &mut Function) {
    let definitions: HashMap<Value, InstKind> = function
        .blocks()
        .flat_map(|(_, block)| &block.insts)
        .filter_map(|inst| inst.result.map(|result| (result, inst.kind.clone())))
        .collect();
    let mut incoming: HashMap<BlockId, Vec<Target>> = HashMap::new();
    for (_, block) in function.blocks() {
        if let Some(term) = &block.term {
            for target in term.targets() {
                incoming
                    .entry(target.block)
                    .or_default()
                    .push(target.clone());
            }
        }
    }

    let proved: Vec<(BlockId, Value, Value)> = function
        .blocks()
        .filter_map(|(header, block)| {
            let Terminator::Branch {
                condition, then, ..
            } = block.term.as_ref()?
            else {
                return None;
            };
            let InstKind::Binary {
                op: BinaryOp::Less,
                left: index,
                right: bound,
            } = definitions.get(condition)?
            else {
                return None;
            };
            let InstKind::Length { receiver } = definitions.get(bound)? else {
                return None;
            };
            if !is_list(function.type_of(*receiver))
                || !ascending_index(function, header, *index, &definitions, &incoming)
            {
                return None;
            }
            Some((then.block, *receiver, *index))
        })
        .collect();

    for (block, receiver, index) in proved {
        for inst in &mut function.block_mut(block).insts {
            let replacement = match inst.kind {
                InstKind::GetIndex {
                    receiver: held,
                    index: at,
                } if held == receiver && at == index => Some(InstKind::GetUncheckedIndex {
                    receiver: held,
                    index: at,
                }),
                InstKind::SetIndex {
                    receiver: held,
                    index: at,
                    value,
                } if held == receiver && at == index => Some(InstKind::SetUncheckedIndex {
                    receiver: held,
                    index: at,
                    value,
                }),
                _ => None,
            };
            if let Some(replacement) = replacement {
                inst.kind = replacement;
                continue;
            }
            if inst.kind.effect() == Effect::State {
                break;
            }
        }
    }
}

fn is_list(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Builtin {
            kind: Builtin::List | Builtin::FrozenList,
            ..
        }
    )
}

fn ascending_index(
    function: &Function,
    header: BlockId,
    index: Value,
    definitions: &HashMap<Value, InstKind>,
    incoming: &HashMap<BlockId, Vec<Target>>,
) -> bool {
    let Some(position) = function
        .block(header)
        .params
        .iter()
        .position(|param| *param == index)
    else {
        return false;
    };
    let Some(edges) = incoming.get(&header) else {
        return false;
    };
    let mut seed = false;
    let mut step = false;
    for edge in edges {
        let Some(value) = edge.args.get(position) else {
            return false;
        };
        match definitions.get(value) {
            Some(InstKind::Const(Const::Int(held))) if *held <= i64::MAX as u64 => seed = true,
            Some(InstKind::Binary {
                op: BinaryOp::Add,
                left,
                right,
            }) if *left == index && positive_integer(*right, definitions) => step = true,
            _ => return false,
        }
    }
    seed && step
}

fn positive_integer(value: Value, definitions: &HashMap<Value, InstKind>) -> bool {
    matches!(
        definitions.get(&value),
        Some(InstKind::Const(Const::Int(held))) if *held > 0 && *held <= i64::MAX as u64
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inst::Inst;
    use crate::program::Function;
    use luar_diagnostics::{FileId, Span};

    const SPAN: Span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };

    #[test]
    fn ascending_length_bound_removes_the_check() {
        let mut function = loop_function(0, false);
        eliminate(&mut function);
        assert!(has_unchecked_access(&function));
    }

    #[test]
    fn negative_start_keeps_the_check() {
        let mut function = loop_function(u64::MAX, false);
        eliminate(&mut function);
        assert!(!has_unchecked_access(&function));
    }

    #[test]
    fn mutation_before_the_access_keeps_the_check() {
        let mut function = loop_function(0, true);
        eliminate(&mut function);
        assert!(!has_unchecked_access(&function));
    }

    fn has_unchecked_access(function: &Function) -> bool {
        function.blocks().any(|(_, block)| {
            block
                .insts
                .iter()
                .any(|inst| matches!(inst.kind, InstKind::GetUncheckedIndex { .. }))
        })
    }

    fn loop_function(first: u64, mutate: bool) -> Function {
        let list = Ty::Builtin {
            kind: Builtin::List,
            args: vec![Ty::INT],
        };
        let mut function = Function::new("read".to_owned(), vec![list], Ty::Unit, SPAN);
        let entry = function.entry;
        let receiver = function.block(entry).params[0];
        let header = function.add_block();
        let body = function.add_block();
        let exit = function.add_block();

        let initial = emit(
            &mut function,
            entry,
            InstKind::Const(Const::Int(first)),
            Ty::INT,
        );
        function.block_mut(entry).term = Some(Terminator::Jump(Target::new(header, vec![initial])));

        let index = function.add_block_param(header, Ty::INT);
        let length = emit(
            &mut function,
            header,
            InstKind::Length { receiver },
            Ty::INT,
        );
        let condition = emit(
            &mut function,
            header,
            InstKind::Binary {
                op: BinaryOp::Less,
                left: index,
                right: length,
            },
            Ty::Bool,
        );
        function.block_mut(header).term = Some(Terminator::Branch {
            condition,
            then: Target::to(body),
            otherwise: Target::to(exit),
        });

        if mutate {
            emit(
                &mut function,
                body,
                InstKind::ListPop { receiver },
                Ty::Optional(Box::new(Ty::INT)),
            );
        }
        emit(
            &mut function,
            body,
            InstKind::GetIndex { receiver, index },
            Ty::INT,
        );
        let one = emit(&mut function, body, InstKind::Const(Const::Int(1)), Ty::INT);
        let next = emit(
            &mut function,
            body,
            InstKind::Binary {
                op: BinaryOp::Add,
                left: index,
                right: one,
            },
            Ty::INT,
        );
        function.block_mut(body).term = Some(Terminator::Jump(Target::new(header, vec![next])));

        let unit = emit(&mut function, exit, InstKind::Const(Const::Unit), Ty::Unit);
        function.block_mut(exit).term = Some(Terminator::Return(unit));
        function
    }

    fn emit(function: &mut Function, block: BlockId, kind: InstKind, ty: Ty) -> Value {
        let value = function.add_value(ty);
        function.block_mut(block).insts.push(Inst {
            result: Some(value),
            kind,
            span: SPAN,
        });
        value
    }
}
