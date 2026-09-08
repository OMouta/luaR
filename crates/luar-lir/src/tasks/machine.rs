//! One async function as a state machine (LR27, LR27.2, LR27.3).
//!
//! The function keeps its name and becomes the call that builds the task: it
//! allocates a frame holding its arguments, and a task whose `poll` closure
//! runs the body over that frame. The body moves to `name#poll`, entered
//! through a switch on the frame's state. Every value live across a
//! suspension lives in the frame: stored where it is defined, loaded where
//! it is used.

use std::collections::{HashMap, HashSet};

use luar_diagnostics::Span;

use crate::inst::{Allocation, Const, Inst, InstKind, Target, Terminator, Trap, Value};
use crate::lower::Gap;
use crate::program::{BlockId, Field, FuncId, Function, Nominal, Program, Shape, Struct};
use crate::ty::TypeId;
use crate::ty::{Builtin, Ty};

use super::build::Builder;
use super::runtime::{Runtime, list_of_dynamic};
use super::{
    CHILDREN, COMPLETION, DELIVERED, POLL, QUEUED, REQUEST, SCHEDULER, STARTED, WAITERS, WAITING,
};

/// The frame's fixed fields. The parameters follow, then the spilled values.
const STATE: u32 = 0;
const TASK: u32 = 1;
const RESULT: u32 = 2;
const FIRST_PARAM: u32 = 3;

/// The state the scope join resumes at. Await sites count up from the next.
const JOIN: i64 = 1;
const FIRST_AWAIT: i64 = 2;

pub(super) fn transform(
    program: &mut Program,
    runtime: &Runtime,
    id: FuncId,
    cancelled: Option<TypeId>,
) -> Option<Gap> {
    let span = program.function(id).span;
    if !program.function(id).slots().is_empty() {
        return Some(Gap {
            span,
            what: "an async function taking a local's address".to_owned(),
        });
    }
    let Ty::Builtin {
        kind: Builtin::Result,
        args,
    } = &program.function(id).result
    else {
        return Some(Gap {
            span,
            what: "an async function without a completion".to_owned(),
        });
    };
    let result_ty = args[0].clone();
    let completion_ty = program.function(id).result.clone();
    let task_ty = Ty::Builtin {
        kind: Builtin::Task,
        args: vec![result_ty],
    };
    let closure_ty = Ty::Function {
        asynchronous: false,
        params: Vec::new(),
        result: Box::new(Ty::Bool),
    };

    let placeholder = Function::new(String::new(), Vec::new(), Ty::Unit, span);
    let mut poll = std::mem::replace(program.function_mut(id), placeholder);
    let name = poll.name.clone();
    let params = poll.params.clone();
    let inline = poll.inline;
    let frame_id = program.add_type(Nominal {
        name: format!("{name}#frame"),
        type_params: Vec::new(),
        shape: Shape::Struct(Struct {
            fields: Vec::new(),
            reference: true,
            repr_c: false,
        }),
        span,
    });
    let frame_ty = Ty::Named {
        id: frame_id,
        args: Vec::new(),
    };

    // Every return completes the task through the scope join.
    let old_entry = poll.entry;
    let finish = poll.add_block();
    let finish_param = poll.add_block_param(finish, completion_ty.clone());
    for block in poll.blocks_mut() {
        if let Some(Terminator::Return(value)) = block.term {
            block.term = Some(Terminator::Jump(Target::new(finish, vec![value])));
        }
    }

    let entry = poll.add_block();
    let closure = poll.add_block_param(entry, closure_ty.clone());
    poll.entry = entry;
    poll.params = vec![closure_ty.clone()];
    poll.result = Ty::Bool;
    poll.asynchronous = false;
    poll.name = format!("{name}#poll");

    let mut b = Builder::new(&mut poll, entry, span);
    let frame = b.get(closure, 1, frame_ty.clone());
    let me = b.get(frame, TASK, task_ty.clone());
    let state = b.get(frame, STATE, Ty::INT);
    let fixed: HashSet<Value> = [closure, frame, me, state].into_iter().collect();
    let unreachable = b.block();
    b.switch_to(unreachable);
    b.terminate(Terminator::Trap(Trap::Unreachable));
    let begin = b.block();
    let resume_join = b.block();
    let mut cases = vec![
        (0, Target::to(begin)),
        (JOIN as u64, Target::to(resume_join)),
    ];

    let mut resumes = vec![resume_join];
    let mut awaited = Vec::new();
    let mut next_state = FIRST_AWAIT;
    let mut worklist: Vec<BlockId> = b.function.blocks().map(|(id, _)| id).collect();
    while let Some(block) = worklist.pop() {
        let Some(at) = b.function.block(block).insts.iter().position(|inst| {
            matches!(
                inst.kind,
                InstKind::Await { .. } | InstKind::CancellationPoint
            )
        }) else {
            continue;
        };
        let (inst, post) = split(b.function, block, at);
        let result = inst.result.expect("an await produces a value");
        b.function.block_mut(post).params.push(result);
        b.switch_to(block);
        match inst.kind {
            InstKind::CancellationPoint => expand_point(&mut b, me, post),
            InstKind::Await { task } => {
                let state = next_state;
                next_state += 1;
                let resume = expand_await(&mut b, runtime, frame, me, task, state, post);
                cases.push((state as u64, Target::to(resume)));
                resumes.push(resume);
                awaited.push(task);
            }
            _ => unreachable!(),
        }
        worklist.push(post);
    }

    b.switch_to(entry);
    b.terminate(Terminator::Switch {
        value: state,
        cases,
        default: Target::to(unreachable),
    });

    // LR27.3: a request arriving before the first body instruction completes
    // the task without running it.
    b.switch_to(begin);
    let (request, due) = due_request(&mut b, me);
    let cancelled_start = b.block();
    let run = b.block();
    b.branch(due, cancelled_start, run);
    b.switch_to(cancelled_start);
    let failed = deliver(&mut b, me, request, &completion_ty);
    b.jump_with(finish, vec![failed]);
    b.switch_to(run);
    let loaded = params
        .iter()
        .enumerate()
        .map(|(index, ty)| b.get(frame, FIRST_PARAM + index as u32, ty.clone()))
        .collect();
    b.jump_with(old_entry, loaded);

    // LR27.2: the implicit scope joins its children before the task
    // completes, cancelling them where an exception leaves the body.
    b.switch_to(finish);
    b.set(frame, RESULT, finish_param);
    let failed = threw(&mut b, finish_param);
    let cancel_children = b.block();
    let join = b.block();
    b.branch(failed, cancel_children, join);

    b.switch_to(cancel_children);
    let error = cancellation(&mut b, cancelled);
    let boxed = b.boxed(me);
    b.call(runtime.cancel_children, vec![boxed, error], Ty::Unit);
    b.jump(join);

    b.switch_to(join);
    let boxed = b.boxed(me);
    let next = b.call(
        runtime.next_child,
        vec![boxed],
        Ty::Optional(Box::new(Ty::Dynamic)),
    );
    let has = b.is_some(next);
    let wait_child = b.block();
    let complete = b.block();
    b.branch(has, wait_child, complete);

    b.switch_to(wait_child);
    let child = b.unwrap(next, Ty::Dynamic);
    let boxed = b.boxed(me);
    b.call(runtime.wait, vec![boxed, child], Ty::Unit);
    let joining = b.int(JOIN);
    b.set(frame, STATE, joining);
    let no = b.bool(false);
    b.ret(no);

    b.switch_to(resume_join);
    let none = b.nil(Ty::Optional(Box::new(Ty::Dynamic)));
    b.set(me, WAITING, none);
    let (request, due) = due_request(&mut b, me);
    let deliver_join = b.block();
    b.branch(due, deliver_join, join);

    // An exception already propagating takes precedence over the request.
    b.switch_to(deliver_join);
    let held = b.get(frame, RESULT, completion_ty.clone());
    let failed = threw(&mut b, held);
    let replace = b.block();
    b.branch(failed, cancel_children, replace);
    b.switch_to(replace);
    let failed = deliver(&mut b, me, request, &completion_ty);
    b.set(frame, RESULT, failed);
    b.jump(cancel_children);

    b.switch_to(complete);
    let held = b.get(frame, RESULT, completion_ty.clone());
    let some = b.some(held);
    b.set(me, COMPLETION, some);
    let yes = b.bool(true);
    b.ret(yes);

    // What survives a suspension lives in the frame.
    let live = live_in(&poll);
    let mut spilled: Vec<Value> = Vec::new();
    let mut seen = HashSet::new();
    for value in resumes
        .iter()
        .flat_map(|block| live[block].iter().copied())
        .chain(awaited.iter().copied())
    {
        if fixed.contains(&value) || matches!(poll.type_of(value), Ty::Never) || !seen.insert(value)
        {
            continue;
        }
        spilled.push(value);
    }
    spilled.sort_unstable();

    let mut fields = vec![
        Field {
            name: "state".to_owned(),
            ty: Ty::INT,
        },
        Field {
            name: "task".to_owned(),
            ty: task_ty.clone(),
        },
        Field {
            name: "result".to_owned(),
            ty: completion_ty.clone(),
        },
    ];
    let mut slots: HashMap<Value, u32> = HashMap::new();
    for (index, param) in poll.block(old_entry).params.clone().into_iter().enumerate() {
        slots.insert(param, FIRST_PARAM + index as u32);
        fields.push(Field {
            name: format!("param{index}"),
            ty: params[index].clone(),
        });
    }
    for value in &spilled {
        if slots.contains_key(value) {
            continue;
        }
        let slot = u32::try_from(fields.len()).expect("frame field count fits in u32");
        slots.insert(*value, slot);
        fields.push(Field {
            name: format!("v{}", value.0),
            ty: poll.type_of(*value).clone(),
        });
    }
    let spilled: HashSet<Value> = spilled.into_iter().collect();
    spill(&mut poll, frame, &spilled, &slots, span);

    let field_types: Vec<Ty> = fields.iter().map(|field| field.ty.clone()).collect();
    if let Shape::Struct(structure) = &mut program.nominal_mut(frame_id).shape {
        structure.fields = fields;
    }
    let poll_id = program.add_function(poll);

    let mut stub = Function::new(name, params, task_ty.clone(), span);
    stub.asynchronous = true;
    stub.inline = inline;
    let stub_entry = stub.entry;
    let args = stub.block(stub_entry).params.clone();
    let mut b = Builder::new(&mut stub, stub_entry, span);
    let mut initial = Vec::with_capacity(field_types.len());
    initial.push(b.int(0));
    initial.push(b.nil(task_ty.clone()));
    initial.push(b.nil(completion_ty.clone()));
    initial.extend(args);
    for ty in &field_types[initial.len()..] {
        initial.push(placeholder_of(&mut b, ty));
    }
    let frame = b.emit(
        InstKind::MakeStruct {
            ty: frame_ty.clone(),
            fields: initial,
            allocation: Allocation::Managed,
        },
        frame_ty,
    );
    let poll_closure = b.emit(
        InstKind::MakeClosure {
            func: poll_id,
            captures: vec![frame],
        },
        closure_ty,
    );
    let completion = b.nil(Ty::Optional(Box::new(completion_ty)));
    let started = b.bool(false);
    let request = b.nil(Ty::Optional(Box::new(Ty::Dynamic)));
    let delivered = b.bool(false);
    let queued = b.bool(false);
    let waiting = b.nil(Ty::Optional(Box::new(Ty::Dynamic)));
    let waiters = empty_list(&mut b);
    let children = empty_list(&mut b);
    let scheduler = b.nil(Ty::Dynamic);
    let mut task_fields = vec![Value(0); super::task_fields(&Ty::Unit).len()];
    task_fields[POLL as usize] = poll_closure;
    task_fields[COMPLETION as usize] = completion;
    task_fields[STARTED as usize] = started;
    task_fields[REQUEST as usize] = request;
    task_fields[DELIVERED as usize] = delivered;
    task_fields[QUEUED as usize] = queued;
    task_fields[WAITING as usize] = waiting;
    task_fields[WAITERS as usize] = waiters;
    task_fields[CHILDREN as usize] = children;
    task_fields[SCHEDULER as usize] = scheduler;
    let task = b.emit(
        InstKind::MakeStruct {
            ty: task_ty.clone(),
            fields: task_fields,
            allocation: Allocation::Managed,
        },
        task_ty,
    );
    b.set(frame, TASK, task);
    b.ret(task);
    *program.function_mut(id) = stub;
    None
}

/// Moves what follows instruction `at` into a new block, and takes the
/// instruction out.
fn split(function: &mut Function, block: BlockId, at: usize) -> (Inst, BlockId) {
    let post = function.add_block();
    let rest = function.block_mut(block).insts.split_off(at + 1);
    let inst = function
        .block_mut(block)
        .insts
        .pop()
        .expect("the split instruction exists");
    let term = function.block_mut(block).term.take();
    let moved = function.block_mut(post);
    moved.insts = rest;
    moved.term = term;
    (inst, post)
}

/// The task's pending request, and whether it is still to be delivered.
fn due_request(b: &mut Builder<'_>, me: Value) -> (Value, Value) {
    let request = b.get(me, REQUEST, Ty::Optional(Box::new(Ty::Dynamic)));
    let delivered = b.get(me, DELIVERED, Ty::Bool);
    let pending = b.is_some(request);
    let undelivered = b.not(delivered);
    let due = b.and(pending, undelivered);
    (request, due)
}

/// Marks the request delivered and builds the completion carrying it.
fn deliver(b: &mut Builder<'_>, me: Value, request: Value, completion_ty: &Ty) -> Value {
    let yes = b.bool(true);
    b.set(me, DELIVERED, yes);
    let error = b.unwrap(request, Ty::Dynamic);
    b.emit(
        InstKind::MakeEnum {
            ty: completion_ty.clone(),
            variant: 1,
            payload: vec![error],
        },
        completion_ty.clone(),
    )
}

fn threw(b: &mut Builder<'_>, completion: Value) -> Value {
    let tag = b.emit(InstKind::GetTag { value: completion }, Ty::INT);
    let one = b.int(1);
    b.equal(tag, one)
}

/// LR27.3: the exception cancellation delivers, `Cancelled {}` from
/// `std/async` (STD22).
fn cancellation(b: &mut Builder<'_>, cancelled: Option<TypeId>) -> Value {
    let error = match cancelled {
        Some(id) => {
            let ty = Ty::Named {
                id,
                args: Vec::new(),
            };
            b.emit(
                InstKind::MakeStruct {
                    ty: ty.clone(),
                    fields: Vec::new(),
                    allocation: Allocation::Managed,
                },
                ty,
            )
        }
        None => {
            let message = b.emit(InstKind::Const(Const::Str("cancelled".to_owned())), Ty::Str);
            b.emit(InstKind::MakeError { message }, Ty::Error)
        }
    };
    b.boxed(error)
}

fn expand_point(b: &mut Builder<'_>, me: Value, post: BlockId) {
    let (request, due) = due_request(b, me);
    let deliver = b.block();
    let skip = b.block();
    b.branch(due, deliver, skip);
    b.switch_to(deliver);
    let yes = b.bool(true);
    b.set(me, DELIVERED, yes);
    b.jump_with(post, vec![request]);
    b.switch_to(skip);
    let none = b.nil(Ty::Optional(Box::new(Ty::Dynamic)));
    b.jump_with(post, vec![none]);
}

/// LR27: the completion once there is one; otherwise start the task where
/// it is unstarted, record the wait, and suspend at `state`. Resumption
/// delivers a pending request first (LR27.3).
fn expand_await(
    b: &mut Builder<'_>,
    runtime: &Runtime,
    frame: Value,
    me: Value,
    task: Value,
    state: i64,
    post: BlockId,
) -> BlockId {
    let Ty::Builtin {
        kind: Builtin::Task,
        args,
    } = b.function.type_of(task).clone()
    else {
        unreachable!("an await takes a task");
    };
    let completion_ty = Ty::Builtin {
        kind: Builtin::Result,
        args: vec![args[0].clone(), Ty::Dynamic],
    };
    let retry = b.block();
    let ready = b.block();
    let check = b.block();
    let start = b.block();
    let wait = b.block();
    let resume = b.block();
    let deliver_here = b.block();
    b.jump(retry);

    b.switch_to(retry);
    let completion = b.get(
        task,
        COMPLETION,
        Ty::Optional(Box::new(completion_ty.clone())),
    );
    let has = b.is_some(completion);
    b.branch(has, ready, check);

    b.switch_to(ready);
    let held = b.unwrap(completion, completion_ty.clone());
    b.jump_with(post, vec![held]);

    b.switch_to(check);
    let started = b.get(task, STARTED, Ty::Bool);
    b.branch(started, wait, start);

    b.switch_to(start);
    let parent = b.boxed(me);
    let child = b.boxed(task);
    b.call(runtime.start, vec![parent, child], Ty::Unit);
    b.jump(wait);

    b.switch_to(wait);
    let waiter = b.boxed(me);
    let on = b.boxed(task);
    b.call(runtime.wait, vec![waiter, on], Ty::Unit);
    let state = b.int(state);
    b.set(frame, STATE, state);
    let no = b.bool(false);
    b.ret(no);

    b.switch_to(resume);
    let none = b.nil(Ty::Optional(Box::new(Ty::Dynamic)));
    b.set(me, WAITING, none);
    let (request, due) = due_request(b, me);
    b.branch(due, deliver_here, retry);

    b.switch_to(deliver_here);
    let failed = deliver(b, me, request, &completion_ty);
    b.jump_with(post, vec![failed]);
    resume
}

fn empty_list(b: &mut Builder<'_>) -> Value {
    b.emit(
        InstKind::MakeList {
            element: Ty::Dynamic,
            values: Vec::new(),
        },
        list_of_dynamic(),
    )
}

/// A value of `ty` for a frame field nothing has written yet.
fn placeholder_of(b: &mut Builder<'_>, ty: &Ty) -> Value {
    let literal = match ty {
        Ty::Unit => Const::Unit,
        Ty::Bool => Const::Bool(false),
        Ty::Int(_) | Ty::Pointer { .. } => Const::Int(0),
        Ty::Float(_) => Const::Float(0.0),
        Ty::Char => Const::Char('\0'),
        _ => Const::Nil,
    };
    b.emit(InstKind::Const(literal), ty.clone())
}

/// The values live on entry to each block, before its parameters.
fn live_in(function: &Function) -> HashMap<BlockId, HashSet<Value>> {
    let blocks: Vec<BlockId> = function.blocks().map(|(id, _)| id).collect();
    let mut live: HashMap<BlockId, HashSet<Value>> =
        blocks.iter().map(|id| (*id, HashSet::new())).collect();
    loop {
        let mut changed = false;
        for &id in blocks.iter().rev() {
            let block = function.block(id);
            let mut held: HashSet<Value> = HashSet::new();
            if let Some(term) = &block.term {
                for target in term.targets() {
                    held.extend(
                        live[&target.block]
                            .iter()
                            .copied()
                            .filter(|value| !function.block(target.block).params.contains(value)),
                    );
                    held.extend(target.args.iter().copied());
                }
                match term {
                    Terminator::Branch { condition, .. } => {
                        held.insert(*condition);
                    }
                    Terminator::Switch { value, .. } | Terminator::Return(value) => {
                        held.insert(*value);
                    }
                    Terminator::Jump(_) | Terminator::Trap(_) => {}
                }
            }
            for inst in block.insts.iter().rev() {
                if let Some(result) = inst.result {
                    held.remove(&result);
                }
                held.extend(inst.kind.operands());
            }
            for param in &block.params {
                held.remove(param);
            }
            if held != live[&id] {
                live.insert(id, held);
                changed = true;
            }
        }
        if !changed {
            return live;
        }
    }
}

/// Stores each spilled value into its frame slot where it is defined, and
/// loads it where it is used.
fn spill(
    function: &mut Function,
    frame: Value,
    spilled: &HashSet<Value>,
    slots: &HashMap<Value, u32>,
    span: Span,
) {
    let blocks: Vec<BlockId> = function.blocks().map(|(id, _)| id).collect();
    for id in blocks {
        let params = function.block(id).params.clone();
        let insts = std::mem::take(&mut function.block_mut(id).insts);
        let mut rebuilt = Vec::with_capacity(insts.len());
        for param in params {
            if spilled.contains(&param) {
                rebuilt.push(store(frame, slots[&param], param, span));
            }
        }
        for mut inst in insts {
            let mut loads = Vec::new();
            inst.kind.values_mut(|value| {
                if spilled.contains(value) {
                    let loaded = function.add_value(function.type_of(*value).clone());
                    loads.push(load(frame, slots[value], loaded, span));
                    *value = loaded;
                }
            });
            rebuilt.extend(loads);
            let result = inst.result;
            rebuilt.push(inst);
            if let Some(result) = result
                && spilled.contains(&result)
            {
                rebuilt.push(store(frame, slots[&result], result, span));
            }
        }
        if let Some(term) = &mut function.block_mut(id).term.clone() {
            let mut loads = Vec::new();
            let mut rename = |value: &mut Value| {
                if spilled.contains(value) {
                    let loaded = function.add_value(function.type_of(*value).clone());
                    loads.push(load(frame, slots[value], loaded, span));
                    *value = loaded;
                }
            };
            match term {
                Terminator::Jump(target) => target.args.iter_mut().for_each(&mut rename),
                Terminator::Branch {
                    condition,
                    then,
                    otherwise,
                } => {
                    rename(condition);
                    then.args.iter_mut().for_each(&mut rename);
                    otherwise.args.iter_mut().for_each(&mut rename);
                }
                Terminator::Switch {
                    value,
                    cases,
                    default,
                } => {
                    rename(value);
                    for (_, target) in cases.iter_mut() {
                        target.args.iter_mut().for_each(&mut rename);
                    }
                    default.args.iter_mut().for_each(&mut rename);
                }
                Terminator::Return(value) => rename(value),
                Terminator::Trap(_) => {}
            }
            rebuilt.extend(loads);
            function.block_mut(id).term = Some(term.clone());
        }
        function.block_mut(id).insts = rebuilt;
    }
}

fn store(frame: Value, field: u32, value: Value, span: Span) -> Inst {
    Inst {
        result: None,
        kind: InstKind::SetField {
            object: frame,
            field,
            value,
        },
        span,
    }
}

fn load(frame: Value, field: u32, result: Value, span: Span) -> Inst {
    Inst {
        result: Some(result),
        kind: InstKind::GetField {
            object: frame,
            field,
        },
        span,
    }
}
