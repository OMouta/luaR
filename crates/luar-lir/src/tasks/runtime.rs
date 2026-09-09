//! The scheduler every program with a task carries: a FIFO queue of runnable
//! tasks, and the operations on erased task handles that starting, waiting,
//! waking, joining, and cancelling need (LR27, LR27.2, LR27.3).

use luar_diagnostics::Span;

use crate::inst::{InstKind, Target, Terminator};
use crate::program::{Field, FuncId, Function, Nominal, Program, Shape, Struct};
use crate::ty::TypeId;
use crate::ty::{Builtin, Ty};

use super::build::Builder;
use super::{
    ACTIVE_SCOPE, COMPLETION, OBSERVED, OWNER, POLL, QUEUED, REQUEST, SCHEDULER, SCOPE_CHILDREN,
    SCOPE_FAILURES, SCOPE_PARENT, SCOPE_REQUEST, STARTED, WAITERS, WAITING, erased_task,
    scope_type,
};

/// The runnable queue and where its next entry sits.
pub(super) const QUEUE: u32 = 0;
pub(super) const HEAD: u32 = 1;

pub(super) struct Runtime {
    pub scheduler: TypeId,
    pub enqueue: FuncId,
    pub start: FuncId,
    pub wake: FuncId,
    pub cancel: FuncId,
    pub cancel_children: FuncId,
    pub cancel_scope: FuncId,
    pub next_child: FuncId,
    pub child_error: FuncId,
    pub wait: FuncId,
    pub drive: FuncId,
}

pub(super) fn list_of_dynamic() -> Ty {
    Ty::Builtin {
        kind: Builtin::List,
        args: vec![Ty::Dynamic],
    }
}

fn optional_dynamic() -> Ty {
    Ty::Optional(Box::new(Ty::Dynamic))
}

fn erased_completion() -> Ty {
    Ty::Builtin {
        kind: Builtin::Result,
        args: vec![Ty::Unit, Ty::Dynamic],
    }
}

fn poll_closure() -> Ty {
    Ty::Function {
        asynchronous: false,
        params: Vec::new(),
        result: Box::new(Ty::Bool),
    }
}

pub(super) fn declare(program: &mut Program, span: Span) -> Runtime {
    let scheduler = program.add_type(Nominal {
        name: "#Scheduler".to_owned(),
        type_params: Vec::new(),
        shape: Shape::Struct(Struct {
            fields: vec![
                Field {
                    name: "queue".to_owned(),
                    ty: list_of_dynamic(),
                },
                Field {
                    name: "head".to_owned(),
                    ty: Ty::INT,
                },
            ],
            reference: true,
            repr_c: false,
        }),
        span,
    });
    let scheduler_ty = Ty::Named {
        id: scheduler,
        args: Vec::new(),
    };

    let enqueue = program.add_function(reserved("#task.enqueue", 2, span));
    let start = program.add_function(reserved("#task.start", 2, span));
    let wake = program.add_function(reserved("#task.wake", 1, span));
    let cancel = program.add_function(reserved("#task.cancel", 2, span));
    let cancel_children = program.add_function(reserved("#task.cancelChildren", 2, span));
    let cancel_scope = program.add_function(reserved("#scope.cancel", 2, span));
    let next_child = {
        let mut function = reserved("#task.nextChild", 1, span);
        function.result = optional_dynamic();
        program.add_function(function)
    };
    let wait = program.add_function(reserved("#task.wait", 2, span));
    let child_error = {
        let mut function = reserved("#task.childError", 1, span);
        function.result = optional_dynamic();
        program.add_function(function)
    };
    let drive = program.add_function(reserved("#task.drive", 2, span));
    let runtime = Runtime {
        scheduler,
        enqueue,
        start,
        wake,
        cancel,
        cancel_children,
        cancel_scope,
        next_child,
        child_error,
        wait,
        drive,
    };

    define_enqueue(program.function_mut(enqueue), &scheduler_ty, span);
    define_start(program.function_mut(start), &runtime, span);
    let cancelled = program.find_type("std/async.Cancelled");
    define_wake(program.function_mut(wake), &runtime, cancelled, span);
    define_cancel(program.function_mut(cancel), &runtime, span);
    define_cancel_children(program.function_mut(cancel_children), &runtime, span);
    define_cancel_scope(program.function_mut(cancel_scope), &runtime, span);
    define_next_child(program.function_mut(next_child), span);
    define_child_error(program.function_mut(child_error), span);
    define_wait(program.function_mut(wait), span);
    define_drive(program.function_mut(drive), &runtime, &scheduler_ty, span);
    runtime
}

/// A function over `arity` erased handles, returning nothing until defined.
fn reserved(name: &str, arity: usize, span: Span) -> Function {
    Function::new(name.to_owned(), vec![Ty::Dynamic; arity], Ty::Unit, span)
}

/// Whether `task` is in the queue already, and appending it where it is not
/// (LR27.3).
fn define_enqueue(function: &mut Function, scheduler_ty: &Ty, span: Span) {
    let entry = function.entry;
    let sched = function.block(entry).params[0];
    let task = function.block(entry).params[1];
    let mut b = Builder::new(function, entry, span);
    let t = b.unboxed(task, erased_task());
    let queued = b.get(t, QUEUED, Ty::Bool);
    let push = b.block();
    let done = b.block();
    b.branch(queued, done, push);

    b.switch_to(push);
    let yes = b.bool(true);
    b.set(t, QUEUED, yes);
    let s = b.unboxed(sched, scheduler_ty.clone());
    let queue = b.get(s, QUEUE, list_of_dynamic());
    b.emit_void(InstKind::ListPush {
        receiver: queue,
        value: task,
    });
    b.jump(done);

    b.switch_to(done);
    let unit = b.unit();
    b.ret(unit);
}

/// LR27.2: starting a task makes the starting task's scope its owner and
/// queues it.
fn define_start(function: &mut Function, runtime: &Runtime, span: Span) {
    let entry = function.entry;
    let parent = function.block(entry).params[0];
    let child = function.block(entry).params[1];
    let mut b = Builder::new(function, entry, span);
    let c = b.unboxed(child, erased_task());
    let p = b.unboxed(parent, erased_task());
    let sched = b.get(p, SCHEDULER, Ty::Dynamic);
    b.set(c, SCHEDULER, sched);
    let scope = b.get(p, ACTIVE_SCOPE, scope_type());
    let boxed_scope = b.boxed(scope);
    let owner = b.some(boxed_scope);
    b.set(c, OWNER, owner);
    let children = b.get(scope, SCOPE_CHILDREN, list_of_dynamic());
    b.emit_void(InstKind::ListPush {
        receiver: children,
        value: child,
    });
    let request = b.get(scope, SCOPE_REQUEST, optional_dynamic());
    let cancelled = b.is_some(request);
    let cancel = b.block();
    let enqueue = b.block();
    let done = b.block();
    b.branch(cancelled, cancel, enqueue);
    b.switch_to(cancel);
    let error = b.unwrap(request, Ty::Dynamic);
    b.call(runtime.cancel, vec![child, error], Ty::Unit);
    b.jump(done);
    b.switch_to(enqueue);
    let yes = b.bool(true);
    b.set(c, STARTED, yes);
    b.call(runtime.enqueue, vec![sched, child], Ty::Unit);
    b.jump(done);
    b.switch_to(done);
    let unit = b.unit();
    b.ret(unit);
}

/// LR27: completion queues the suspended awaiters in the order they began
/// waiting. LR27.2: child failures cancel siblings and enter the owner's
/// failure list in completion order; `Cancelled` is excluded.
fn define_wake(function: &mut Function, runtime: &Runtime, cancelled: Option<TypeId>, span: Span) {
    let entry = function.entry;
    let task = function.block(entry).params[0];
    let mut b = Builder::new(function, entry, span);
    let t = b.unboxed(task, erased_task());
    let owner = b.get(t, OWNER, optional_dynamic());
    let owned = b.is_some(owner);
    let inspect = b.block();
    let notify = b.block();
    b.branch(owned, inspect, notify);
    b.switch_to(inspect);
    let completion = b.get(t, COMPLETION, Ty::Optional(Box::new(erased_completion())));
    let completion = b.unwrap(completion, erased_completion());
    let tag = b.emit(InstKind::GetTag { value: completion }, Ty::INT);
    let one = b.int(1);
    let failed = b.equal(tag, one);
    let failure = b.block();
    b.branch(failed, failure, notify);
    b.switch_to(failure);
    let error = b.emit(
        InstKind::GetPayload {
            value: completion,
            variant: 1,
            field: 0,
        },
        Ty::Dynamic,
    );
    let record = b.block();
    if let Some(id) = cancelled {
        let is_cancelled = b.emit(
            InstKind::IsType {
                value: error,
                ty: Ty::Named {
                    id,
                    args: Vec::new(),
                },
            },
            Ty::Bool,
        );
        b.branch(is_cancelled, notify, record);
    } else {
        b.jump(record);
    }
    b.switch_to(record);
    let parent = b.unwrap(owner, Ty::Dynamic);
    let p = b.unboxed(parent, scope_type());
    let failures = b.get(p, SCOPE_FAILURES, list_of_dynamic());
    b.emit_void(InstKind::ListPush {
        receiver: failures,
        value: task,
    });
    let cancellation = super::machine::cancellation(&mut b, cancelled);
    b.call(runtime.cancel_scope, vec![parent, cancellation], Ty::Unit);
    b.jump(notify);
    b.switch_to(notify);
    let waiters = b.get(t, WAITERS, list_of_dynamic());
    let count = b.length(waiters);
    let head = b.block();
    let index = b.param(head, Ty::INT);
    let body = b.block();
    let end = b.block();
    let zero = b.int(0);
    b.jump_with(head, vec![zero]);

    b.switch_to(head);
    let finished = b.equal(index, count);
    b.branch(finished, end, body);

    b.switch_to(body);
    let waiter = b.index(waiters, index, Ty::Dynamic);
    let w = b.unboxed(waiter, erased_task());
    let sched = b.get(w, SCHEDULER, Ty::Dynamic);
    b.call(runtime.enqueue, vec![sched, waiter], Ty::Unit);
    let one = b.int(1);
    let next = b.add(index, one);
    b.jump_with(head, vec![next]);

    b.switch_to(end);
    b.emit_void(InstKind::Clear { receiver: waiters });
    let unit = b.unit();
    b.ret(unit);
}

/// LR27.3: one request per task. An unstarted task completes with it; a
/// started one passes it to its children and is queued to receive it.
fn define_cancel(function: &mut Function, runtime: &Runtime, span: Span) {
    let entry = function.entry;
    let task = function.block(entry).params[0];
    let error = function.block(entry).params[1];
    let mut b = Builder::new(function, entry, span);
    let t = b.unboxed(task, erased_task());
    let completion = b.get(t, COMPLETION, Ty::Optional(Box::new(erased_completion())));
    let completed = b.is_some(completion);
    let pending = b.block();
    let done = b.block();
    b.branch(completed, done, pending);

    b.switch_to(pending);
    let request = b.get(t, REQUEST, optional_dynamic());
    let requested = b.is_some(request);
    let mark = b.block();
    b.branch(requested, done, mark);

    b.switch_to(mark);
    let request = b.some(error);
    b.set(t, REQUEST, request);
    let started = b.get(t, STARTED, Ty::Bool);
    let propagate = b.block();
    let unstarted = b.block();
    b.branch(started, propagate, unstarted);

    b.switch_to(unstarted);
    let failed = b.emit(
        InstKind::MakeEnum {
            ty: erased_completion(),
            variant: 1,
            payload: vec![error],
        },
        erased_completion(),
    );
    let completion = b.some(failed);
    b.set(t, COMPLETION, completion);
    b.jump(done);

    b.switch_to(propagate);
    b.call(runtime.cancel_children, vec![task, error], Ty::Unit);
    let sched = b.get(t, SCHEDULER, Ty::Dynamic);
    b.call(runtime.enqueue, vec![sched, task], Ty::Unit);
    b.jump(done);

    b.switch_to(done);
    let unit = b.unit();
    b.ret(unit);
}

/// LR27.2, LR27.3: a request on a scope reaches every unfinished child.
fn define_cancel_children(function: &mut Function, runtime: &Runtime, span: Span) {
    let entry = function.entry;
    let task = function.block(entry).params[0];
    let error = function.block(entry).params[1];
    let mut b = Builder::new(function, entry, span);
    let t = b.unboxed(task, erased_task());
    let active = b.get(t, ACTIVE_SCOPE, scope_type());
    let walk = b.block();
    let scope = b.param(walk, scope_type());
    let next = b.block();
    let done = b.block();
    b.jump_with(walk, vec![active]);
    b.switch_to(walk);
    let shielded = b.get(scope, super::SCOPE_SHIELDED, Ty::Bool);
    let mark = b.block();
    let follow = b.block();
    b.branch(shielded, follow, mark);
    b.switch_to(mark);
    let request = b.some(error);
    b.set(scope, SCOPE_REQUEST, request);
    let boxed = b.boxed(scope);
    b.call(runtime.cancel_scope, vec![boxed, error], Ty::Unit);
    b.jump(follow);
    b.switch_to(follow);
    let parent = b.get(scope, SCOPE_PARENT, Ty::Optional(Box::new(scope_type())));
    let has_parent = b.is_some(parent);
    b.branch(has_parent, next, done);
    b.switch_to(next);
    let parent = b.unwrap(parent, scope_type());
    b.jump_with(walk, vec![parent]);
    b.switch_to(done);
    let unit = b.unit();
    b.ret(unit);
}

fn define_cancel_scope(function: &mut Function, runtime: &Runtime, span: Span) {
    let entry = function.entry;
    let task = function.block(entry).params[0];
    let error = function.block(entry).params[1];
    let mut b = Builder::new(function, entry, span);
    let t = b.unboxed(task, scope_type());
    let children = b.get(t, SCOPE_CHILDREN, list_of_dynamic());
    let count = b.length(children);
    let head = b.block();
    let index = b.param(head, Ty::INT);
    let body = b.block();
    let end = b.block();
    let zero = b.int(0);
    b.jump_with(head, vec![zero]);

    b.switch_to(head);
    let finished = b.equal(index, count);
    b.branch(finished, end, body);

    b.switch_to(body);
    let child = b.index(children, index, Ty::Dynamic);
    b.call(runtime.cancel, vec![child, error], Ty::Unit);
    let one = b.int(1);
    let next = b.add(index, one);
    b.jump_with(head, vec![next]);

    b.switch_to(end);
    let unit = b.unit();
    b.ret(unit);
}

/// LR27.2: the first child a scope still has to wait for, or nothing.
fn define_next_child(function: &mut Function, span: Span) {
    let entry = function.entry;
    let task = function.block(entry).params[0];
    let mut b = Builder::new(function, entry, span);
    let t = b.unboxed(task, scope_type());
    let children = b.get(t, SCOPE_CHILDREN, list_of_dynamic());
    let count = b.length(children);
    let head = b.block();
    let index = b.param(head, Ty::INT);
    let body = b.block();
    let step = b.block();
    let found = b.block();
    let none = b.block();
    let zero = b.int(0);
    b.jump_with(head, vec![zero]);

    b.switch_to(head);
    let finished = b.equal(index, count);
    b.branch(finished, none, body);

    b.switch_to(body);
    let child = b.index(children, index, Ty::Dynamic);
    let c = b.unboxed(child, erased_task());
    let completion = b.get(c, COMPLETION, Ty::Optional(Box::new(erased_completion())));
    let completed = b.is_some(completion);
    b.branch(completed, step, found);

    b.switch_to(step);
    let one = b.int(1);
    let next = b.add(index, one);
    b.jump_with(head, vec![next]);

    b.switch_to(found);
    let some = b.some(child);
    b.ret(some);

    b.switch_to(none);
    let nil = b.nil(optional_dynamic());
    b.ret(nil);
}

/// LR27.2: the first unobserved child exception in completion order.
fn define_child_error(function: &mut Function, span: Span) {
    let entry = function.entry;
    let task = function.block(entry).params[0];
    let mut b = Builder::new(function, entry, span);
    let t = b.unboxed(task, scope_type());
    let failures = b.get(t, SCOPE_FAILURES, list_of_dynamic());
    let count = b.length(failures);
    let head = b.block();
    let index = b.param(head, Ty::INT);
    let body = b.block();
    let step = b.block();
    let found = b.block();
    let none = b.block();
    let zero = b.int(0);
    b.jump_with(head, vec![zero]);

    b.switch_to(head);
    let finished = b.equal(index, count);
    b.branch(finished, none, body);
    b.switch_to(body);
    let child = b.index(failures, index, Ty::Dynamic);
    let c = b.unboxed(child, erased_task());
    let observed = b.get(c, OBSERVED, Ty::Bool);
    b.branch(observed, step, found);
    b.switch_to(step);
    let one = b.int(1);
    let next = b.add(index, one);
    b.jump_with(head, vec![next]);
    b.switch_to(found);
    let completion = b.get(c, COMPLETION, Ty::Optional(Box::new(erased_completion())));
    let completion = b.unwrap(completion, erased_completion());
    let error = b.emit(
        InstKind::GetPayload {
            value: completion,
            variant: 1,
            field: 0,
        },
        Ty::Dynamic,
    );
    let some = b.some(error);
    b.ret(some);
    b.switch_to(none);
    let nil = b.nil(optional_dynamic());
    b.ret(nil);
}

/// LR27: a task about to suspend on `on` records that, after checking that
/// the chain of tasks `on` waits for does not lead back to it.
fn define_wait(function: &mut Function, span: Span) {
    let entry = function.entry;
    let me = function.block(entry).params[0];
    let on = function.block(entry).params[1];
    let mut b = Builder::new(function, entry, span);
    let this = b.unboxed(me, erased_task());
    let walk = b.block();
    let current = b.param(walk, Ty::Dynamic);
    let follow = b.block();
    let step = b.block();
    let cycle = b.block();
    let register = b.block();
    b.jump_with(walk, vec![on]);

    b.switch_to(walk);
    let held = b.unboxed(current, erased_task());
    let same = b.equal(held, this);
    b.branch(same, cycle, follow);

    b.switch_to(follow);
    let waiting = b.get(held, WAITING, optional_dynamic());
    let waits = b.is_some(waiting);
    b.branch(waits, step, register);

    b.switch_to(step);
    let next = b.unwrap(waiting, Ty::Dynamic);
    b.jump_with(walk, vec![next]);

    b.switch_to(cycle);
    b.panic("cyclic task await");

    b.switch_to(register);
    let target = b.unboxed(on, erased_task());
    let waiters = b.get(target, WAITERS, list_of_dynamic());
    b.emit_void(InstKind::ListPush {
        receiver: waiters,
        value: me,
    });
    let some = b.some(on);
    b.set(this, WAITING, some);
    let unit = b.unit();
    b.ret(unit);
}

/// LR27, LR27.1: runs queued tasks in order until `until` has completed.
fn define_drive(function: &mut Function, runtime: &Runtime, scheduler_ty: &Ty, span: Span) {
    let entry = function.entry;
    let sched = function.block(entry).params[0];
    let until = function.block(entry).params[1];
    let mut b = Builder::new(function, entry, span);
    let head = b.block();
    let step = b.block();
    let stuck = b.block();
    let pop = b.block();
    let reset = b.block();
    let run = b.block();
    let poll = b.block();
    let woken = b.block();
    let finished = b.block();
    b.jump(head);

    b.switch_to(head);
    let u = b.unboxed(until, erased_task());
    let completion = b.get(u, COMPLETION, Ty::Optional(Box::new(erased_completion())));
    let completed = b.is_some(completion);
    b.branch(completed, finished, step);

    b.switch_to(step);
    let s = b.unboxed(sched, scheduler_ty.clone());
    let queue = b.get(s, QUEUE, list_of_dynamic());
    let at = b.get(s, HEAD, Ty::INT);
    let count = b.length(queue);
    let empty = b.equal(at, count);
    b.branch(empty, stuck, pop);

    b.switch_to(stuck);
    b.panic("no runnable task");

    b.switch_to(pop);
    let task = b.index(queue, at, Ty::Dynamic);
    let one = b.int(1);
    let after = b.add(at, one);
    b.set(s, HEAD, after);
    let drained = b.equal(after, count);
    b.branch(drained, reset, run);

    b.switch_to(reset);
    b.emit_void(InstKind::Clear { receiver: queue });
    let zero = b.int(0);
    b.set(s, HEAD, zero);
    b.jump(run);

    b.switch_to(run);
    let t = b.unboxed(task, erased_task());
    let no = b.bool(false);
    b.set(t, QUEUED, no);
    let completion = b.get(t, COMPLETION, Ty::Optional(Box::new(erased_completion())));
    let completed = b.is_some(completion);
    b.branch(completed, head, poll);

    b.switch_to(poll);
    let closure = b.get(t, POLL, poll_closure());
    let done = b.emit(
        InstKind::CallIndirect {
            callee: closure,
            args: Vec::new(),
        },
        Ty::Bool,
    );
    b.branch(done, woken, head);

    b.switch_to(woken);
    b.call(runtime.wake, vec![task], Ty::Unit);
    b.terminate(Terminator::Jump(Target::to(head)));

    b.switch_to(finished);
    let unit = b.unit();
    b.ret(unit);
}
