//! Tasks: async functions as state machines over a FIFO scheduler (LR27,
//! LR27.1, LR27.2, LR27.3).

mod build;
mod machine;
mod runtime;

use crate::inst::{Allocation, Inst, InstKind};
use crate::lower::Gap;
use crate::program::{FuncId, Function, Program};
use crate::ty::{Builtin, Ty};

use build::Builder;
use runtime::{Runtime, list_of_dynamic};

/// The fields of a `Task<T>`, in the order [`task_fields`] lists them.
pub const POLL: u32 = 0;
pub const COMPLETION: u32 = 1;
pub const STARTED: u32 = 2;
pub const REQUEST: u32 = 3;
pub const DELIVERED: u32 = 4;
pub const QUEUED: u32 = 5;
pub const WAITING: u32 = 6;
pub const WAITERS: u32 = 7;
pub const CHILDREN: u32 = 8;
pub const SCHEDULER: u32 = 9;
pub const OWNER: u32 = 10;
pub const FAILURES: u32 = 11;
pub const OBSERVED: u32 = 12;

/// What a `Task<T>` holds: the closure that advances it and says whether it
/// completed, its completion, whether it started, its cancellation request
/// and whether that was delivered, whether it is queued, the task it waits
/// for, the tasks waiting for it, the children its implicit scope owns, and
/// the scheduler it runs on, its owner, failed children in completion order,
/// and whether an await observed its completion. Only the completion depends
/// on `T`, so a handle can be read as `Task<()>` where `T` is not needed.
#[must_use]
pub fn task_fields(result: &Ty) -> Vec<Ty> {
    let optional_dynamic = Ty::Optional(Box::new(Ty::Dynamic));
    vec![
        Ty::Function {
            asynchronous: false,
            params: Vec::new(),
            result: Box::new(Ty::Bool),
        },
        Ty::Optional(Box::new(Ty::Builtin {
            kind: Builtin::Result,
            args: vec![result.clone(), Ty::Dynamic],
        })),
        Ty::Bool,
        optional_dynamic.clone(),
        Ty::Bool,
        Ty::Bool,
        optional_dynamic,
        list_of_dynamic(),
        list_of_dynamic(),
        Ty::Dynamic,
        Ty::Optional(Box::new(Ty::Dynamic)),
        list_of_dynamic(),
        Ty::Bool,
    ]
}

pub(crate) fn erased_task() -> Ty {
    Ty::Builtin {
        kind: Builtin::Task,
        args: vec![Ty::Unit],
    }
}

/// Runs after monomorphization and before inlining.
pub fn run(program: &mut Program) -> Vec<Gap> {
    let asynchronous: Vec<FuncId> = program
        .functions()
        .filter(|(_, function)| {
            function.asynchronous && !function.is_template() && function.external.is_none()
        })
        .map(|(id, _)| id)
        .collect();
    let Some(&first) = asynchronous.first() else {
        return Vec::new();
    };
    let span = program.function(first).span;
    let runtime = runtime::declare(program, span);
    let cancelled = program.find_type("std/async.Cancelled");
    let mut gaps = Vec::new();
    for id in asynchronous {
        gaps.extend(machine::transform(program, &runtime, id, cancelled));
    }
    expand_cancels(program, &runtime);
    wrap_entry(program, &runtime);
    gaps
}

/// LR27.3: `task:cancel()` anywhere, async or not, is the runtime's request.
fn expand_cancels(program: &mut Program, runtime: &Runtime) {
    let functions: Vec<FuncId> = program.functions().map(|(id, _)| id).collect();
    for id in functions {
        let function = program.function_mut(id);
        let blocks: Vec<_> = function.blocks().map(|(id, _)| id).collect();
        for block in blocks {
            if !function
                .block(block)
                .insts
                .iter()
                .any(|inst| matches!(inst.kind, InstKind::Cancel { .. }))
            {
                continue;
            }
            let insts = std::mem::take(&mut function.block_mut(block).insts);
            let mut rebuilt = Vec::with_capacity(insts.len() + 2);
            for inst in insts {
                let InstKind::Cancel { task, error } = inst.kind else {
                    rebuilt.push(inst);
                    continue;
                };
                let boxed = function.add_value(Ty::Dynamic);
                rebuilt.push(Inst {
                    result: Some(boxed),
                    kind: InstKind::MakeDyn {
                        interface: None,
                        value: task,
                    },
                    span: inst.span,
                });
                let unit = function.add_value(Ty::Unit);
                rebuilt.push(Inst {
                    result: Some(unit),
                    kind: InstKind::Call {
                        callee: runtime.cancel,
                        type_args: Vec::new(),
                        args: vec![boxed, error],
                    },
                    span: inst.span,
                });
            }
            function.block_mut(block).insts = rebuilt;
        }
    }
}

/// LR27.1: an async `main` is started on a fresh scheduler, which runs until
/// it completes; what it completed with is what the process reports.
fn wrap_entry(program: &mut Program, runtime: &Runtime) {
    let Some(entry) = program.entry else {
        return;
    };
    let main = program.function(entry);
    if !main.asynchronous {
        return;
    }
    let Ty::Builtin {
        kind: Builtin::Task,
        args,
    } = &main.result
    else {
        return;
    };
    let completion_ty = Ty::Builtin {
        kind: Builtin::Result,
        args: vec![args[0].clone(), Ty::Dynamic],
    };
    let task_ty = main.result.clone();
    let span = main.span;
    let mut wrapper = Function::new(
        format!("{}#entry", main.name),
        main.params.clone(),
        completion_ty.clone(),
        span,
    );
    let block = wrapper.entry;
    let args = wrapper.block(block).params.clone();
    let mut b = Builder::new(&mut wrapper, block, span);
    let task = b.call(entry, args, task_ty);
    let queue = b.emit(
        InstKind::MakeList {
            element: Ty::Dynamic,
            values: Vec::new(),
        },
        list_of_dynamic(),
    );
    let zero = b.int(0);
    let scheduler_ty = Ty::Named {
        id: runtime.scheduler,
        args: Vec::new(),
    };
    let scheduler = b.emit(
        InstKind::MakeStruct {
            ty: scheduler_ty.clone(),
            fields: vec![queue, zero],
            allocation: Allocation::Managed,
        },
        scheduler_ty,
    );
    let scheduler = b.boxed(scheduler);
    let yes = b.bool(true);
    b.set(task, STARTED, yes);
    b.set(task, SCHEDULER, scheduler);
    let boxed = b.boxed(task);
    b.call(runtime.enqueue, vec![scheduler, boxed], Ty::Unit);
    b.call(runtime.drive, vec![scheduler, boxed], Ty::Unit);
    let completion = b.get(
        task,
        COMPLETION,
        Ty::Optional(Box::new(completion_ty.clone())),
    );
    let held = b.unwrap(completion, completion_ty);
    b.ret(held);
    program.entry = Some(program.add_function(wrapper));
}
