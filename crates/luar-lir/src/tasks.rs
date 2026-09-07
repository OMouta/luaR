//! Deferred task calls and shared completions (LR27).

use std::collections::HashMap;

use luar_diagnostics::Span;

use crate::inst::{Const, Inst, InstKind, Terminator, Value};
use crate::program::{FuncId, Function, Program};
use crate::ty::{Builtin, Ty};

/// Runs after monomorphization and before inlining.
pub fn run(program: &mut Program) {
    let functions: Vec<FuncId> = program
        .functions()
        .filter(|(_, function)| !function.is_template())
        .map(|(id, _)| id)
        .collect();
    for id in functions {
        let blocks: Vec<_> = program.function(id).blocks().map(|(id, _)| id).collect();
        for block in blocks {
            let mut insts = std::mem::take(&mut program.function_mut(id).block_mut(block).insts);
            let tasks: Vec<_> = insts
                .iter()
                .filter_map(|inst| match &inst.kind {
                    InstKind::MakeStruct {
                        ty:
                            Ty::Builtin {
                                kind: Builtin::Task,
                                args,
                            },
                        fields,
                        ..
                    } if args.len() == 1 && fields.len() == 1 => {
                        Some((inst.result.unwrap(), fields[0], args[0].clone(), inst.span))
                    }
                    _ => None,
                })
                .collect();
            for (task, completion, result, span) in tasks {
                let at = insts
                    .iter()
                    .position(|inst| inst.result == Some(completion))
                    .unwrap();
                let mut finish = insts.remove(at);
                let mut call = match &finish.kind {
                    InstKind::MakeEnum { payload, .. } => {
                        let at = insts
                            .iter()
                            .position(|inst| inst.result == Some(payload[0]))
                            .unwrap();
                        Some(insts.remove(at))
                    }
                    _ => None,
                };
                let pending = call.as_mut().unwrap_or(&mut finish);
                let captures = match &pending.kind {
                    InstKind::Call { args, .. } => args.clone(),
                    InstKind::CallIndirect { callee, args } => std::iter::once(*callee)
                        .chain(args.iter().copied())
                        .collect(),
                    InstKind::CallVirtual { receiver, args, .. } => std::iter::once(*receiver)
                        .chain(args.iter().copied())
                        .collect(),
                    _ => unreachable!("a task completion comes from a call"),
                };
                let thunk_ty = Ty::Function {
                    asynchronous: false,
                    params: Vec::new(),
                    result: Box::new(result),
                };
                let completion_ty = program.function(id).type_of(completion).clone();
                let mut thunk = Function::new(
                    format!("{}#task{}", program.function(id).name, task.0),
                    vec![thunk_ty.clone()],
                    completion_ty.clone(),
                    span,
                );
                let closure = thunk.block(thunk.entry).params[0];
                let mut values = HashMap::new();
                for (index, capture) in captures.iter().enumerate() {
                    let value = emit(
                        &mut thunk,
                        InstKind::GetField {
                            object: closure,
                            field: u32::try_from(index + 1).expect("capture count fits in u32"),
                        },
                        program.function(id).type_of(*capture).clone(),
                        span,
                    );
                    values.insert(*capture, value);
                }
                match &mut pending.kind {
                    InstKind::Call { args, .. } => {
                        args.iter_mut().for_each(|arg| *arg = values[arg])
                    }
                    InstKind::CallIndirect { callee, args } => {
                        *callee = values[callee];
                        args.iter_mut().for_each(|arg| *arg = values[arg]);
                    }
                    InstKind::CallVirtual { receiver, args, .. } => {
                        *receiver = values[receiver];
                        args.iter_mut().for_each(|arg| *arg = values[arg]);
                    }
                    _ => unreachable!(),
                }
                if let Some(call) = call {
                    let value = emit(
                        &mut thunk,
                        call.kind,
                        program.function(id).type_of(call.result.unwrap()).clone(),
                        span,
                    );
                    let InstKind::MakeEnum { payload, .. } = &mut finish.kind else {
                        unreachable!()
                    };
                    payload[0] = value;
                }
                let completed = emit(&mut thunk, finish.kind, completion_ty.clone(), span);
                thunk.block_mut(thunk.entry).term = Some(Terminator::Return(completed));
                let func = program.add_function(thunk);
                let closure = program.function_mut(id).add_value(thunk_ty);
                let empty = program
                    .function_mut(id)
                    .add_value(Ty::Optional(Box::new(completion_ty)));
                let at = insts
                    .iter()
                    .position(|inst| inst.result == Some(task))
                    .unwrap();
                let InstKind::MakeStruct { fields, .. } = &mut insts[at].kind else {
                    unreachable!()
                };
                *fields = vec![closure, empty];
                insts.splice(
                    at..at,
                    [
                        Inst {
                            result: Some(closure),
                            kind: InstKind::MakeClosure { func, captures },
                            span,
                        },
                        Inst {
                            result: Some(empty),
                            kind: InstKind::Const(Const::Nil),
                            span,
                        },
                    ],
                );
            }
            program.function_mut(id).block_mut(block).insts = insts;
        }
    }
}

fn emit(function: &mut Function, kind: InstKind, ty: Ty, span: Span) -> Value {
    let value = function.add_value(ty);
    function.block_mut(function.entry).insts.push(Inst {
        result: Some(value),
        kind,
        span,
    });
    value
}
