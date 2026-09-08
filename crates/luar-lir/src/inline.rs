//! Inlining requested by built-in attributes (LR23.2).

use std::collections::HashMap;

use crate::inst::{InstKind, Target, Terminator, Value};
use crate::program::{BlockId, FuncId, Inline, Program, SlotId};

type CallSite = (BlockId, usize, FuncId, Vec<Value>, Option<Value>);

pub fn run(program: &mut Program) {
    let callers: Vec<FuncId> = program.functions().map(|(id, _)| id).collect();

    for caller in callers {
        let mut calls: Vec<CallSite> = program
            .function(caller)
            .blocks()
            .flat_map(|(block, held)| {
                held.insts
                    .iter()
                    .enumerate()
                    .filter_map(move |(at, inst)| match &inst.kind {
                        InstKind::Call {
                            callee,
                            type_args,
                            args,
                        } if type_args.is_empty() => {
                            Some((block, at, *callee, args.clone(), inst.result))
                        }
                        _ => None,
                    })
            })
            .filter(|(_, _, callee, _, _)| *callee != caller && inlineable(program, *callee))
            .collect();
        calls.sort_by_key(|(block, at, _, _, _)| (block.0, *at));

        for (block, at, callee, args, result) in calls.into_iter().rev() {
            inline_call(program, caller, block, at, callee, &args, result);
        }
    }
}

fn inlineable(program: &Program, callee: FuncId) -> bool {
    let function = program.function(callee);
    function.inline == Inline::Always
        && function.external.is_none()
        && !function.asynchronous
        && function.blocks().all(|(_, block)| block.term.is_some())
}

fn inline_call(
    program: &mut Program,
    caller: FuncId,
    block: BlockId,
    at: usize,
    callee: FuncId,
    args: &[Value],
    result: Option<Value>,
) {
    let called = program.function(callee).clone();
    let function = program.function_mut(caller);

    let continuation = function.add_block();
    let (suffix, term) = {
        let source = function.block_mut(block);
        let suffix = source.insts.split_off(at + 1);
        source.insts.pop();
        let term = source.term.take();
        (suffix, term)
    };
    function.block_mut(continuation).insts = suffix;
    function.block_mut(continuation).term = term;
    if let Some(value) = result {
        function.block_mut(continuation).params.push(value);
    }

    let mut values = HashMap::new();
    for (param, argument) in called
        .block(called.entry)
        .params
        .iter()
        .copied()
        .zip(args.iter().copied())
    {
        values.insert(param, argument);
    }
    for (value, ty) in called.values() {
        values
            .entry(value)
            .or_insert_with(|| function.add_value(ty.clone()));
    }

    let slots: HashMap<SlotId, SlotId> = called
        .slots()
        .iter()
        .enumerate()
        .map(|(index, ty)| (SlotId(index as u32), function.add_slot(ty.clone())))
        .collect();
    let blocks: HashMap<BlockId, BlockId> = called
        .blocks()
        .map(|(id, _)| (id, function.add_block()))
        .collect();

    for (source, held) in called.blocks() {
        let target = blocks[&source];
        if source != called.entry {
            function.block_mut(target).params =
                held.params.iter().map(|value| values[value]).collect();
        }
        function.block_mut(target).insts = held
            .insts
            .iter()
            .cloned()
            .map(|mut inst| {
                inst.result = inst.result.map(|value| values[&value]);
                remap_inst(&mut inst.kind, &values, &slots);
                inst
            })
            .collect();
        function.block_mut(target).term = held
            .term
            .as_ref()
            .map(|term| remap_term(term, &values, &blocks, continuation, result.is_some()));
    }

    function.block_mut(block).term = Some(Terminator::Jump(Target::to(blocks[&called.entry])));
}

fn remap_inst(inst: &mut InstKind, map: &HashMap<Value, Value>, slots: &HashMap<SlotId, SlotId>) {
    inst.values_mut(|value| *value = map[value]);
    inst.slots_mut(|slot| *slot = slots[slot]);
}

fn remap_target(
    target: &Target,
    values: &HashMap<Value, Value>,
    blocks: &HashMap<BlockId, BlockId>,
) -> Target {
    Target::new(
        blocks[&target.block],
        target.args.iter().map(|value| values[value]).collect(),
    )
}

fn remap_term(
    term: &Terminator,
    values: &HashMap<Value, Value>,
    blocks: &HashMap<BlockId, BlockId>,
    continuation: BlockId,
    returns_value: bool,
) -> Terminator {
    match term {
        Terminator::Jump(target) => Terminator::Jump(remap_target(target, values, blocks)),
        Terminator::Branch {
            condition,
            then,
            otherwise,
        } => Terminator::Branch {
            condition: values[condition],
            then: remap_target(then, values, blocks),
            otherwise: remap_target(otherwise, values, blocks),
        },
        Terminator::Switch {
            value,
            cases,
            default,
        } => Terminator::Switch {
            value: values[value],
            cases: cases
                .iter()
                .map(|(case, target)| (*case, remap_target(target, values, blocks)))
                .collect(),
            default: remap_target(default, values, blocks),
        },
        Terminator::Return(value) => Terminator::Jump(Target::new(
            continuation,
            returns_value.then(|| values[value]).into_iter().collect(),
        )),
        Terminator::Trap(trap) => Terminator::Trap(*trap),
    }
}
