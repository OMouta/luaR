//! Task-scope entry, spawning, and suspension at joins (LR27.2).

use crate::inst::{Allocation, InstKind, ScopeKind, Value};
use crate::program::BlockId;
use crate::ty::{Ty, TypeId};

use super::build::Builder;
use super::machine::{STATE, cancellation, due_request};
use super::runtime::{Runtime, list_of_dynamic};
use super::{
    ACTIVE_SCOPE, COMPLETION, DELIVERED, ROOT_SCOPE, SCOPE_PARENT, SCOPE_REQUEST, SCOPE_SHIELDED,
    STARTED, WAITING, scope_type,
};

pub(super) fn open(b: &mut Builder<'_>, me: Value, kind: ScopeKind, post: BlockId) {
    if kind == ScopeKind::Implicit {
        let root = b.get(me, ROOT_SCOPE, scope_type());
        b.jump_with(post, vec![root]);
        return;
    }
    let parent = b.get(me, ACTIVE_SCOPE, scope_type());
    let (request, shielded) = if kind == ScopeKind::Cleanup {
        (b.nil(Ty::Optional(Box::new(Ty::Dynamic))), b.bool(true))
    } else {
        (
            b.get(parent, SCOPE_REQUEST, Ty::Optional(Box::new(Ty::Dynamic))),
            b.get(parent, SCOPE_SHIELDED, Ty::Bool),
        )
    };
    let parent = b.some(parent);
    let mut fields = Vec::new();
    for _ in 0..2 {
        fields.push(b.emit(
            InstKind::MakeList {
                element: Ty::Dynamic,
                values: Vec::new(),
            },
            list_of_dynamic(),
        ));
    }
    fields.extend([request, parent, shielded]);
    let scope = b.emit(
        InstKind::MakeStruct {
            ty: scope_type(),
            fields,
            allocation: Allocation::Managed,
        },
        scope_type(),
    );
    b.set(me, ACTIVE_SCOPE, scope);
    b.jump_with(post, vec![scope]);
}

pub(super) fn close(b: &mut Builder<'_>, me: Value, scope: Value, post: BlockId) {
    let parent = b.get(scope, SCOPE_PARENT, Ty::Optional(Box::new(scope_type())));
    let nested = b.is_some(parent);
    let restore = b.block();
    b.branch(nested, restore, post);
    b.switch_to(restore);
    let parent = b.unwrap(parent, scope_type());
    b.set(me, ACTIVE_SCOPE, parent);
    b.jump(post);
}

pub(super) fn cancel(b: &mut Builder<'_>, runtime: &Runtime, scope: Value, error: Value) {
    let request = b.some(error);
    b.set(scope, SCOPE_REQUEST, request);
    let scope = b.boxed(scope);
    b.call(runtime.cancel_scope, vec![scope, error], Ty::Unit);
}

pub(super) fn spawn(
    b: &mut Builder<'_>,
    runtime: &Runtime,
    me: Value,
    scope: Value,
    task: Value,
    post: BlockId,
) {
    let started = b.get(task, STARTED, Ty::Bool);
    let fields = super::task_fields(&Ty::Unit);
    let completion = b.get(task, COMPLETION, fields[COMPLETION as usize].clone());
    let completed = b.is_some(completion);
    let check = b.block();
    let panic = b.block();
    let start = b.block();
    b.branch(started, panic, check);
    b.switch_to(check);
    b.branch(completed, panic, start);
    b.switch_to(panic);
    b.panic("spawn requires an unstarted task");
    b.switch_to(start);
    let active = b.get(me, ACTIVE_SCOPE, scope_type());
    b.set(me, ACTIVE_SCOPE, scope);
    let parent = b.boxed(me);
    let child = b.boxed(task);
    b.call(runtime.start, vec![parent, child], Ty::Unit);
    b.set(me, ACTIVE_SCOPE, active);
    b.jump_with(post, vec![task]);
}

#[allow(clippy::too_many_arguments)]
pub(super) fn join(
    b: &mut Builder<'_>,
    runtime: &Runtime,
    frame: Value,
    me: Value,
    scope: Value,
    abrupt: bool,
    propagating: bool,
    cancelled: Option<TypeId>,
    state: i64,
    post: BlockId,
) -> BlockId {
    if abrupt {
        let error = cancellation(b, cancelled);
        cancel(b, runtime, scope, error);
    }
    let retry = b.block();
    let error = b.param(retry, Ty::Optional(Box::new(Ty::Dynamic)));
    let inspect = b.block();
    let deliver = b.block();
    let wait = b.block();
    let complete = b.block();
    let resume = b.block();
    let none = b.nil(Ty::Optional(Box::new(Ty::Dynamic)));
    b.jump_with(retry, vec![none]);

    b.switch_to(retry);
    let (request, due) = due_request(b, me);
    b.branch(due, deliver, inspect);
    b.switch_to(deliver);
    let yes = b.bool(true);
    b.set(me, DELIVERED, yes);
    let exception = b.unwrap(request, Ty::Dynamic);
    cancel(b, runtime, scope, exception);
    b.jump_with(retry, vec![request]);

    b.switch_to(inspect);
    let boxed_scope = b.boxed(scope);
    let next = b.call(
        runtime.next_child,
        vec![boxed_scope],
        Ty::Optional(Box::new(Ty::Dynamic)),
    );
    let pending = b.is_some(next);
    b.branch(pending, wait, complete);
    b.switch_to(wait);
    let child = b.unwrap(next, Ty::Dynamic);
    let boxed_me = b.boxed(me);
    b.call(runtime.wait, vec![boxed_me, child], Ty::Unit);
    let state = b.int(state);
    b.set(frame, STATE, state);
    let no = b.bool(false);
    b.ret(no);
    b.switch_to(resume);
    let none = b.nil(Ty::Optional(Box::new(Ty::Dynamic)));
    b.set(me, WAITING, none);
    b.jump_with(retry, vec![error]);

    b.switch_to(complete);
    if propagating {
        let none = b.nil(Ty::Optional(Box::new(Ty::Dynamic)));
        b.jump_with(post, vec![none]);
    } else {
        let cancelled = b.is_some(error);
        let preserve = b.block();
        let select = b.block();
        b.branch(cancelled, preserve, select);
        b.switch_to(preserve);
        b.jump_with(post, vec![error]);
        b.switch_to(select);
        let scope = b.boxed(scope);
        let error = b.call(
            runtime.child_error,
            vec![scope],
            Ty::Optional(Box::new(Ty::Dynamic)),
        );
        b.jump_with(post, vec![error]);
    }
    resume
}
