//! One LIR function in Cranelift IR.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    self, AbiParam, Block, FuncRef, GlobalValue, InstBuilder, MemFlags, Signature, StackSlot,
    TrapCode, Type, types,
};
use cranelift_frontend::{FunctionBuilder, Switch};
use luar_lir::inst::{Const, Inst, InstKind, Terminator, Trap, Value};
use luar_lir::program::{BlockId, FuncId, Function, Program, SlotId};
use luar_lir::ty::{Builtin, Ty, TypeId};

use crate::Gap;
use crate::layout::{self, TAG, TAG_TYPE};
use crate::ty::machine;

mod arith;
mod calls;
mod list;
mod memory;
mod roots;

/// Storage the program built is its own, so nothing else writes it and every
/// access to it is in range.
const OWNED: MemFlags = MemFlags::trusted();

/// Storage a raw pointer names is whatever the program said it is (LR72).
const FOREIGN: MemFlags = MemFlags::new();

/// The trap kinds, in the order the handler table holds them.
pub(crate) const TRAPS: [Trap; 4] = [
    Trap::IntegerOverflow,
    Trap::DivisionByZero,
    Trap::Bounds,
    Trap::Unreachable,
];

/// Where `trap`'s handler sits in that table.
#[must_use]
pub(crate) fn handler_index(trap: Trap) -> usize {
    TRAPS
        .iter()
        .position(|kind| *kind == trap)
        .expect("every trap kind is in the table")
}

/// What the machine does after the handler, which never returns. Cranelift
/// needs a terminator there and no program reaches it.
const AFTER_HANDLER: TrapCode = TrapCode::unwrap_user(1);
const ASSERTION_FAILURE: i64 = 0;
const PANIC_FAILURE: i64 = 1;

/// The Cranelift signature of `function`, or `None` where a parameter or the
/// result has a type the backend cannot represent yet.
pub(crate) fn signature(
    function: &Function,
    pointer: Type,
    call_conv: cranelift_codegen::isa::CallConv,
) -> Option<Signature> {
    let mut signature = Signature::new(call_conv);
    for param in &function.params {
        signature
            .params
            .push(AbiParam::new(machine(param, pointer)?));
    }
    if function.external.is_none() || function.result != Ty::Unit {
        signature
            .returns
            .push(AbiParam::new(machine(&function.result, pointer)?));
    }
    Some(signature)
}

pub(crate) struct Translator<'a, 'b> {
    pub program: &'a Program,
    pub function: &'a Function,
    pub function_name: GlobalValue,
    pub function_name_length: usize,
    pub builder: FunctionBuilder<'b>,
    pub pointer: Type,
    pub callees: HashMap<FuncId, FuncRef>,
    /// The data object each literal text lives in, by its bytes.
    pub texts: HashMap<Vec<u8>, GlobalValue>,
    /// The runtime handler for each trap kind, in [`TRAPS`] order.
    pub handlers: [FuncRef; TRAPS.len()],
    /// Where managed aggregate storage comes from (LR29).
    pub allocate: FuncRef,
    pub concat: FuncRef,
    pub text_equal: FuncRef,
    pub hash_bytes: FuncRef,
    pub display_signed: FuncRef,
    pub display_unsigned: FuncRef,
    pub print: FuncRef,
    pub abort: FuncRef,
    /// The bucket a map holds a key in, and the bucket it will (LR13.2).
    pub map_find: FuncRef,
    pub map_insert: FuncRef,
    pub map_remove: FuncRef,
    pub finalizers: HashMap<Ty, FuncRef>,
    /// The global holding the top shadow-stack frame.
    pub roots: GlobalValue,
    pub root_frame: Option<StackSlot>,
    pub root_offsets: HashMap<Value, i32>,
    pub temporary_roots: Vec<i32>,
    pub blocks: HashMap<BlockId, Block>,
    pub values: HashMap<Value, ir::Value>,
    /// The stack storage of each LIR slot (LR72).
    pub slots: HashMap<SlotId, StackSlot>,
    /// The identity of each type a dynamic value can hold (LR25.3).
    pub descriptors: HashMap<Ty, GlobalValue>,
    /// The method table of each implementation an interface value can carry
    /// (LR18.1).
    pub vtables: HashMap<(TypeId, Ty), GlobalValue>,
    pub gaps: Vec<Gap>,
}

impl Translator<'_, '_> {
    /// Walks every block, in the order the function holds them, and gives
    /// back what it could not emit.
    pub fn run(mut self) -> Vec<Gap> {
        self.create_blocks();
        self.create_slots();
        self.prepare_roots();

        let entry = self.blocks[&self.function.entry];
        self.builder.append_block_params_for_function_params(entry);
        let params = self.function.block(self.function.entry).params.clone();
        for (index, param) in params.iter().enumerate() {
            let value = self.builder.block_params(entry)[index];
            self.values.insert(*param, value);
        }

        let ids: Vec<BlockId> = self.function.blocks().map(|(id, _)| id).collect();
        for id in ids {
            self.block(id);
        }

        self.builder.seal_all_blocks();
        self.builder.finalize();
        self.gaps
    }

    fn create_blocks(&mut self) {
        let ids: Vec<BlockId> = self.function.blocks().map(|(id, _)| id).collect();
        for id in ids {
            let created = self.builder.create_block();
            self.blocks.insert(id, created);

            // The entry block takes the function's parameters, which Cranelift
            // appends from the signature rather than one at a time.
            if id == self.function.entry {
                continue;
            }
            for param in self.function.block(id).params.clone() {
                let ty = self.machine_or_gap(param);
                let value = self.builder.append_block_param(created, ty);
                self.values.insert(param, value);
            }
        }
    }

    fn block(&mut self, id: BlockId) {
        let block = self.blocks[&id];
        self.builder.switch_to_block(block);

        if id == self.function.entry {
            self.enter_roots();
        }
        for param in self.function.block(id).params.clone() {
            let value = self.value(param);
            self.root(param, value);
        }

        for inst in self.function.block(id).insts.clone() {
            self.inst(&inst);
        }

        match self.function.block(id).term.clone() {
            Some(term) => self.terminator(&term),
            None => {
                self.gap("a block with no terminator");
                self.raise(Trap::Unreachable);
            }
        }
    }

    fn terminator(&mut self, term: &Terminator) {
        match term {
            Terminator::Jump(target) => {
                let block = self.blocks[&target.block];
                let args = self.block_args(&target.args);
                self.builder.ins().jump(block, &args);
            }
            Terminator::Branch {
                condition,
                then,
                otherwise,
            } => {
                let condition = self.value(*condition);
                let then_block = self.blocks[&then.block];
                let then_args = self.block_args(&then.args);
                let else_block = self.blocks[&otherwise.block];
                let else_args = self.block_args(&otherwise.args);
                self.builder
                    .ins()
                    .brif(condition, then_block, &then_args, else_block, &else_args);
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                let scrutinee = self.value(*value);
                let mut switch = Switch::new();
                for (tag, target) in cases {
                    // A `Switch` reaches blocks that take no arguments,
                    // because lowering reads a payload after the jump rather
                    // than passing it (LR16).
                    if !target.args.is_empty() {
                        self.gap("a switch case that passes arguments");
                    }
                    switch.set_entry(u128::from(*tag), self.blocks[&target.block]);
                }
                if !default.args.is_empty() {
                    self.gap("a switch default that passes arguments");
                }
                let otherwise = self.blocks[&default.block];
                switch.emit(&mut self.builder, scrutinee, otherwise);
            }
            Terminator::Return(value) => {
                if self.function.type_of(*value) == &Ty::Never {
                    self.raise(Trap::Unreachable);
                    return;
                }
                let value = self.value(*value);
                self.leave_roots();
                self.builder.ins().return_(&[value]);
            }
            Terminator::Trap(trap) => self.raise(*trap),
        }
    }

    fn block_args(&mut self, args: &[Value]) -> Vec<ir::BlockArg> {
        args.iter()
            .map(|arg| ir::BlockArg::Value(self.value(*arg)))
            .collect()
    }

    fn inst(&mut self, inst: &Inst) {
        let produced = match &inst.kind {
            InstKind::Const(literal) => self.constant(literal, inst.result),
            InstKind::Unary { op, operand } => self.unary(*op, *operand),
            InstKind::Binary { op, left, right } => self.binary(*op, *left, *right),
            InstKind::HashValue { value } => self.hash_value(*value),
            InstKind::HashCombine { state, value } => {
                let state = self.value(*state);
                let value = self.value(*value);
                let mixed = self.builder.ins().bxor(state, value);
                Some(self.builder.ins().imul_imm(mixed, 0x100000001b3))
            }
            InstKind::DisplayValue { value } => self.display_value(*value),
            InstKind::Print { value } => {
                let value = self.value(*value);
                self.builder.ins().call(self.print, &[value]);
                None
            }
            InstKind::MakeError { message } => Some(self.value(*message)),
            InstKind::Assert { condition, message } => {
                self.assert(*condition, *message);
                None
            }
            InstKind::Panic { message } => {
                let message = self.value(*message);
                let kind = self.builder.ins().iconst(types::I8, PANIC_FAILURE);
                let call = self.builder.ins().call(self.abort, &[kind, message]);
                self.builder.inst_results(call).first().copied()
            }
            InstKind::Convert { value, to } => self.convert(*value, to),
            InstKind::Call {
                callee,
                type_args,
                args,
            } => self.call(*callee, type_args, args),

            InstKind::CopyValue { value } => {
                let ty = self.function.type_of(*value).clone();
                let source = self.value(*value);
                self.duplicate(source, &ty, layout::DEPTH)
            }
            InstKind::Freeze { value } => Some(self.value(*value)),
            InstKind::MakeStruct { ty, fields } => self.make(ty, 0, fields),

            // LR9.8: a closure is its code's address and then what it
            // captured, and it is passed to that code first.
            InstKind::MakeClosure { func, captures } => {
                let ty = inst
                    .result
                    .map(|value| self.function.type_of(value).clone());
                let reference = self.callees.get(func).copied();
                match (ty, reference) {
                    (Some(ty), Some(reference)) => {
                        let cells = i32::try_from(captures.len() + 1).unwrap_or(i32::MAX);
                        let built = self.allocate_bytes(layout::CELL * cells, &ty, 0);
                        built.inspect(|&built| {
                            let code = self.builder.ins().func_addr(self.pointer, reference);
                            self.builder.ins().store(OWNED, code, built, 0);
                            for (index, capture) in captures.iter().enumerate() {
                                let cell =
                                    u32::try_from(index + 1).expect("capture count fits in u32");
                                self.write_at(built, &ty, cell, *capture);
                            }
                        })
                    }
                    (_, None) => {
                        self.gap("a closure over code the backend did not emit");
                        None
                    }
                    (None, _) => None,
                }
            }
            InstKind::CallIndirect { callee, args } => self.call_indirect(*callee, args),
            InstKind::CallVirtual {
                method,
                receiver,
                args,
            } => self.call_virtual(*method, *receiver, args),

            // A dynamic value is what it is, and then what it holds (LR18.1,
            // LR25.3).
            InstKind::MakeDyn { interface, value } => {
                self.make_dyn(*interface, *value, inst.result)
            }
            InstKind::DynValue { value } => self.read(*value, 1, inst.result),
            InstKind::IsType { value, ty } => {
                if *self.function.type_of(*value) != Ty::Dynamic {
                    self.gap("a type test on a value that is not dynamic");
                    None
                } else if let Some(descriptor) = self.descriptors.get(ty).copied() {
                    let object = self.value(*value);
                    let held = self.builder.ins().load(self.pointer, OWNED, object, 0);
                    let wanted = self.builder.ins().global_value(self.pointer, descriptor);
                    Some(self.builder.ins().icmp(IntCC::Equal, held, wanted))
                } else {
                    self.gap(format!("a type test against `{ty}`"));
                    None
                }
            }
            InstKind::MakeTuple(members) => {
                let ty = inst
                    .result
                    .map(|value| self.function.type_of(value).clone());
                match ty {
                    Some(ty) => self.make(&ty, 0, members),
                    None => None,
                }
            }
            InstKind::MakeEnum {
                ty,
                variant,
                payload,
            } => self.make(ty, 1, payload).inspect(|&built| {
                let tag = self.builder.ins().iconst(TAG_TYPE, i64::from(*variant));
                self.builder.ins().store(OWNED, tag, built, TAG);
            }),
            InstKind::GetField { object, field } => self.read(*object, *field, inst.result),
            InstKind::GetElement { tuple, index } => self.read(*tuple, *index, inst.result),
            // The tag has already proved the variant, so the payload sits
            // where that variant put it.
            InstKind::GetPayload { value, field, .. } => self.read(*value, field + 1, inst.result),
            InstKind::SetField {
                object,
                field,
                value,
            } => {
                self.write(*object, *field, *value);
                None
            }
            InstKind::GetTag { value } => {
                let object = self.value(*value);
                Some(self.builder.ins().load(TAG_TYPE, OWNED, object, TAG))
            }

            // LR8: an optional holds whether it holds anything, and then what.
            InstKind::MakeSome { value } => {
                let ty = inst.result.map(|held| self.function.type_of(held).clone());
                let built = ty.as_ref().and_then(|ty| self.allocate(ty, 0));
                built.inspect(|&built| {
                    let present = self.builder.ins().iconst(TAG_TYPE, 1);
                    self.builder.ins().store(OWNED, present, built, TAG);
                    self.write_at(built, ty.as_ref().expect("a result type"), 1, *value);
                })
            }
            InstKind::IsSome { value } => {
                let object = self.value(*value);
                let tag = self.builder.ins().load(TAG_TYPE, OWNED, object, TAG);
                let absent = self.builder.ins().iconst(TAG_TYPE, 0);
                Some(self.builder.ins().icmp(IntCC::NotEqual, tag, absent))
            }
            InstKind::Unwrap { value } => self.read(*value, 1, inst.result),

            InstKind::MakeList { values, .. } => self.make_list(inst.result, values),
            InstKind::MakeMap { entries, .. } => self.make_map(inst.result, entries),
            InstKind::MakeSet { values, .. } => self.make_set(inst.result, values),
            InstKind::ListPushAll { receiver, other } => {
                self.list_push_all(*receiver, *other);
                None
            }
            InstKind::ListPush { receiver, value } => {
                self.list_push(*receiver, *value);
                None
            }
            InstKind::ListPop { receiver } => self.list_pop(*receiver, inst.result),
            InstKind::ListInsert {
                receiver,
                index,
                value,
            } => {
                self.list_insert(*receiver, *index, *value);
                None
            }
            InstKind::ListRemoveAt { receiver, index } => self.list_remove_at(*receiver, *index),
            InstKind::SetInsert { receiver, value } => {
                self.set_insert(*receiver, *value);
                None
            }
            InstKind::Contains { receiver, value } => self.contains(*receiver, *value),
            InstKind::IndexOf { receiver, value } => self.index_of(*receiver, *value, inst.result),
            InstKind::MapRemove { receiver, key } => self.map_remove(*receiver, *key, inst.result),
            InstKind::SetRemove { receiver, value } => self.set_remove(*receiver, *value),
            InstKind::ListReverse { receiver } => {
                self.list_reverse(*receiver);
                None
            }
            InstKind::Clear { receiver } => {
                self.clear(*receiver);
                None
            }
            InstKind::Overflowing {
                mode,
                op,
                left,
                right,
            } => self.overflowing(*mode, *op, *left, *right, inst.result),
            InstKind::Length { receiver } => {
                let list = self.value(*receiver);
                Some(
                    self.builder
                        .ins()
                        .load(self.pointer, OWNED, list, layout::LENGTH),
                )
            }
            InstKind::Buckets { receiver } => {
                let table = self.value(*receiver);
                Some(
                    self.builder
                        .ins()
                        .load(self.pointer, OWNED, table, layout::CAPACITY),
                )
            }
            InstKind::Occupied { receiver, index } => {
                let bucket = self.bucket_address(*receiver, *index);
                let occupied =
                    self.builder
                        .ins()
                        .load(self.pointer, OWNED, bucket, layout::BUCKET_OCCUPIED);
                Some(self.builder.ins().icmp_imm(IntCC::NotEqual, occupied, 0))
            }
            InstKind::EntryKey { receiver, index } => {
                let bucket = self.bucket_address(*receiver, *index);
                let word = self
                    .builder
                    .ins()
                    .load(self.pointer, OWNED, bucket, layout::BUCKET_KEY);
                let ty = inst
                    .result
                    .map_or(self.pointer, |value| self.machine_or_gap(value));
                Some(if ty.bits() < self.pointer.bits() {
                    self.builder.ins().ireduce(ty, word)
                } else {
                    word
                })
            }
            InstKind::EntryValue { receiver, index } => {
                let bucket = self.bucket_address(*receiver, *index);
                let ty = inst
                    .result
                    .map_or(types::I8, |value| self.machine_or_gap(value));
                Some(
                    self.builder
                        .ins()
                        .load(ty, OWNED, bucket, layout::BUCKET_VALUE),
                )
            }
            InstKind::GetIndex { receiver, index } => {
                self.get_index(*receiver, *index, inst.result)
            }
            InstKind::GetCheckedIndex { receiver, index } => {
                self.get_checked_index(*receiver, *index, inst.result)
            }
            InstKind::SetIndex {
                receiver,
                index,
                value,
            } => {
                self.set_index(*receiver, *index, *value);
                None
            }

            InstKind::SlotGet { slot } => match self.slots.get(slot).copied() {
                Some(stack) => {
                    let ty = inst
                        .result
                        .map_or(types::I8, |value| self.machine_or_gap(value));
                    Some(self.builder.ins().stack_load(ty, stack, 0))
                }
                None => None,
            },
            InstKind::SlotSet { slot, value } => {
                if let Some(stack) = self.slots.get(slot).copied() {
                    let written = self.value(*value);
                    self.builder.ins().stack_store(written, stack, 0);
                }
                None
            }
            InstKind::FieldAddress { object, field, .. } => {
                let held = self.function.type_of(*object).clone();
                let target = inst
                    .result
                    .map(|result| self.function.type_of(result).clone());
                match target {
                    Some(Ty::Pointer { target, .. }) if layout::is_aggregate(&target) => {
                        self.gap("an address of an aggregate field");
                        None
                    }
                    _ => layout::field_offset(self.program, &held, *field, self.pointer).map(
                        |offset| {
                            let address = self.value(*object);
                            self.builder.ins().iadd_imm(address, i64::from(offset))
                        },
                    ),
                }
            }
            InstKind::Offset { pointer, count } => {
                let target = match self.function.type_of(*pointer) {
                    Ty::Pointer { target, .. } => target.as_ref().clone(),
                    other => other.clone(),
                };
                match machine(&target, self.pointer) {
                    Some(stride) if !layout::is_aggregate(&target) => {
                        let address = self.value(*pointer);
                        let count = self.value(*count);
                        let bytes = self
                            .builder
                            .ins()
                            .imul_imm(count, i64::from(stride.bytes()));
                        Some(self.builder.ins().iadd(address, bytes))
                    }
                    _ => {
                        self.gap("pointer arithmetic over aggregates");
                        None
                    }
                }
            }
            InstKind::Load { pointer } => match inst.result {
                Some(result) if layout::is_aggregate(self.function.type_of(result)) => {
                    self.gap("a read of an aggregate through a pointer");
                    None
                }
                Some(result) => {
                    let address = self.value(*pointer);
                    let ty = self.machine_or_gap(result);
                    Some(self.builder.ins().load(ty, FOREIGN, address, 0))
                }
                None => None,
            },
            InstKind::Store { pointer, value } => {
                if layout::is_aggregate(self.function.type_of(*value)) {
                    self.gap("a write of an aggregate through a pointer");
                } else {
                    let address = self.value(*pointer);
                    let written = self.value(*value);
                    self.builder.ins().store(FOREIGN, written, address, 0);
                }
                None
            }
            InstKind::TextBytes { text } => {
                let text = self.value(*text);
                Some(self.builder.ins().iadd_imm(text, i64::from(layout::CELL)))
            }
            InstKind::MakeText { data, length } => self.make_text(*data, *length),
            // An aggregate already sits in storage of its own, and its slot
            // holds the pointer to it, so that pointer is its address.
            InstKind::AddressOf { slot, .. } => match self.slots.get(slot).copied() {
                Some(stack) if layout::is_aggregate(self.function.slot_type(*slot)) => {
                    Some(self.builder.ins().stack_load(self.pointer, stack, 0))
                }
                Some(stack) => Some(self.builder.ins().stack_addr(self.pointer, stack, 0)),
                None => None,
            },
        };

        let Some(result) = inst.result else {
            return;
        };
        let value = match produced {
            Some(value) => value,
            // The gap beside it says the program does less than its source
            // does; the placeholder keeps the function well formed.
            None => {
                let ty = self.machine_or_gap(result);
                self.builder.ins().iconst(ty, 0)
            }
        };
        self.values.insert(result, value);
        self.root(result, value);
    }

    fn constant(&mut self, literal: &Const, result: Option<Value>) -> Option<ir::Value> {
        // LR8: `nil` in an optional's place is storage that holds nothing.
        if let Const::Nil = literal
            && let Some(result) = result
            && let ty @ Ty::Optional(_) = self.function.type_of(result).clone()
        {
            let built = self.allocate(&ty, 0)?;
            let absent = self.builder.ins().iconst(TAG_TYPE, 0);
            self.builder.ins().store(OWNED, absent, built, TAG);
            return Some(built);
        }

        let ty = result.map_or(types::I8, |value| self.machine_or_gap(value));
        let value = match literal {
            Const::Unit => self.builder.ins().iconst(types::I8, 0),
            Const::Bool(set) => self.builder.ins().iconst(types::I8, i64::from(*set)),
            // The bits are the bits of the value's own type, and Cranelift
            // reads the width from the type it is given here.
            Const::Int(bits) => self.builder.ins().iconst(ty, *bits as i64),
            Const::Char(scalar) => {
                let scalar = i64::from(u32::from(*scalar));
                self.builder.ins().iconst(types::I32, scalar)
            }
            Const::Str(text) => return self.text(text.as_bytes()),
            Const::Bytes(bytes) => return self.text(bytes),
            Const::Nil | Const::Float(_) => {
                self.gap("a literal that is not an integer, a boolean, or a character");
                return None;
            }
        };
        Some(value)
    }

    fn hash_value(&mut self, value: Value) -> Option<ir::Value> {
        let ty = self.function.type_of(value);
        let value = self.value(value);
        match ty {
            Ty::Str | Ty::Bytes => {
                let call = self.builder.ins().call(self.hash_bytes, &[value]);
                self.builder.inst_results(call).first().copied()
            }
            Ty::Unit | Ty::Nil => Some(self.builder.ins().iconst(types::I64, 0)),
            Ty::Bool | Ty::Int(_) | Ty::Char => {
                let held = self.builder.func.dfg.value_type(value);
                Some(match held.bits().cmp(&64) {
                    std::cmp::Ordering::Less => self.builder.ins().uextend(types::I64, value),
                    std::cmp::Ordering::Equal => value,
                    std::cmp::Ordering::Greater => self.builder.ins().ireduce(types::I64, value),
                })
            }
            _ => {
                self.gap(format!("hashing a value of type `{ty}`"));
                None
            }
        }
    }

    fn display_value(&mut self, value: Value) -> Option<ir::Value> {
        let ty = self.function.type_of(value);
        let value = self.value(value);
        match ty {
            Ty::Str => Some(value),
            Ty::Int(int) => {
                let held = self.builder.func.dfg.value_type(value);
                let widened = match held.bits().cmp(&64) {
                    std::cmp::Ordering::Less if int.is_signed() => {
                        self.builder.ins().sextend(types::I64, value)
                    }
                    std::cmp::Ordering::Less => self.builder.ins().uextend(types::I64, value),
                    std::cmp::Ordering::Equal => value,
                    std::cmp::Ordering::Greater => self.builder.ins().ireduce(types::I64, value),
                };
                let formatter = if int.is_signed() {
                    self.display_signed
                } else {
                    self.display_unsigned
                };
                let call = self.builder.ins().call(formatter, &[widened]);
                self.builder.inst_results(call).first().copied()
            }
            _ => {
                self.gap(format!("displaying a value of type `{ty}`"));
                None
            }
        }
    }

    /// The address of a literal's text, which lives in the object rather than
    /// being built at runtime (LR4.5).
    fn text(&mut self, bytes: &[u8]) -> Option<ir::Value> {
        let Some(&data) = self.texts.get(bytes) else {
            self.gap("a literal the object has no text for");
            return None;
        };
        Some(self.builder.ins().global_value(self.pointer, data))
    }

    /// LR72: a string holding `length` bytes copied from `data`.
    fn make_text(&mut self, data: Value, length: Value) -> Option<ir::Value> {
        let data = self.value(data);
        let length = self.value(length);
        let cell = i64::from(layout::CELL);
        let size = self.builder.ins().iadd_imm(length, cell + cell - 1);
        let size = self.builder.ins().band_imm(size, -cell);
        let size = self.word_of(size);
        let text = self.allocate_sized(size, &Ty::Str, 0)?;
        self.builder
            .ins()
            .store(OWNED, length, text, layout::LENGTH);

        let copy = self.builder.create_block();
        let copy_one = self.builder.create_block();
        let done = self.builder.create_block();
        self.builder.append_block_param(copy, self.pointer);
        self.builder.append_block_param(copy_one, self.pointer);
        let zero = self.builder.ins().iconst(self.pointer, 0);
        self.builder.ins().jump(copy, &[ir::BlockArg::Value(zero)]);

        self.builder.switch_to_block(copy);
        let index = self.builder.block_params(copy)[0];
        let more = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, index, length);
        self.builder
            .ins()
            .brif(more, copy_one, &[ir::BlockArg::Value(index)], done, &[]);

        self.builder.switch_to_block(copy_one);
        let index = self.builder.block_params(copy_one)[0];
        let from = self.builder.ins().iadd(data, index);
        let byte = self.builder.ins().load(types::I8, OWNED, from, 0);
        let to = self.builder.ins().iadd(text, index);
        self.builder.ins().store(OWNED, byte, to, layout::CELL);
        let following = self.builder.ins().iadd_imm(index, 1);
        self.builder
            .ins()
            .jump(copy, &[ir::BlockArg::Value(following)]);

        self.builder.switch_to_block(done);
        Some(text)
    }

    /// LR13.2: a map starts empty and takes its entries one at a time, so
    /// the runtime decides its capacity.
    fn make_map(&mut self, result: Option<Value>, entries: &[(Value, Value)]) -> Option<ir::Value> {
        let ty = self.function.type_of(result?).clone();
        let Ty::Builtin { args, .. } = &ty else {
            return None;
        };
        let text = self.compared_by_text(args.first()?)?;
        let header = self.allocate(&ty, 0)?;
        let zero = self.builder.ins().iconst(self.pointer, 0);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::LENGTH);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::CAPACITY);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::BUFFER);
        for (key, value) in entries {
            let bucket = self.map_insert(header, *key, text)?;
            let written = self.value(*value);
            self.builder
                .ins()
                .store(OWNED, written, bucket, layout::BUCKET_VALUE);
        }
        Some(header)
    }

    /// LR13.3: a set stores each distinct value as a table key.
    fn make_set(&mut self, result: Option<Value>, values: &[Value]) -> Option<ir::Value> {
        let ty = self.function.type_of(result?).clone();
        let Ty::Builtin { args, .. } = &ty else {
            return None;
        };
        let text = self.compared_by_text(args.first()?)?;
        let header = self.allocate(&ty, 0)?;
        let zero = self.builder.ins().iconst(self.pointer, 0);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::LENGTH);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::CAPACITY);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::BUFFER);
        for value in values {
            self.map_insert(header, *value, text)?;
        }
        Some(header)
    }

    fn set_insert(&mut self, receiver: Value, value: Value) {
        let held = self.function.type_of(receiver).clone();
        let Ty::Builtin {
            kind: Builtin::Set,
            args,
        } = &held
        else {
            self.gap(format!("inserting into `{held}`"));
            return;
        };
        let Some(text) = args
            .first()
            .and_then(|element| self.compared_by_text(element))
        else {
            return;
        };
        let set = self.value(receiver);
        let _ = self.map_insert(set, value, text);
    }

    fn map_remove(
        &mut self,
        receiver: Value,
        key: Value,
        result: Option<Value>,
    ) -> Option<ir::Value> {
        let optional = self.function.type_of(result?).clone();
        let Ty::Optional(inner) = &optional else {
            self.gap("a removal that is not optional");
            return None;
        };
        let Some(machine) = machine(inner, self.pointer) else {
            self.gap(format!("a map holding `{inner}`"));
            return None;
        };
        let bucket = self.find_bucket(receiver, key)?;
        let table = self.value(receiver);
        let present = self.builder.ins().icmp_imm(IntCC::NotEqual, bucket, 0);
        let built = self.allocate(&optional, 0)?;
        let tag = self.builder.ins().uextend(TAG_TYPE, present);
        self.builder.ins().store(OWNED, tag, built, TAG);

        let found = self.builder.create_block();
        let carry_on = self.builder.create_block();
        self.builder.ins().brif(present, found, &[], carry_on, &[]);
        self.builder.switch_to_block(found);
        let value = self
            .builder
            .ins()
            .load(machine, OWNED, bucket, layout::BUCKET_VALUE);
        self.builder.ins().store(OWNED, value, built, layout::CELL);
        self.builder.ins().call(self.map_remove, &[table, bucket]);
        self.builder.ins().jump(carry_on, &[]);
        self.builder.switch_to_block(carry_on);
        Some(built)
    }

    fn set_remove(&mut self, receiver: Value, value: Value) -> Option<ir::Value> {
        let bucket = self.find_bucket(receiver, value)?;
        let table = self.value(receiver);
        let present = self.builder.ins().icmp_imm(IntCC::NotEqual, bucket, 0);
        let found = self.builder.create_block();
        let carry_on = self.builder.create_block();
        self.builder.ins().brif(present, found, &[], carry_on, &[]);
        self.builder.switch_to_block(found);
        self.builder.ins().call(self.map_remove, &[table, bucket]);
        self.builder.ins().jump(carry_on, &[]);
        self.builder.switch_to_block(carry_on);
        Some(present)
    }

    fn clear(&mut self, receiver: Value) {
        let held = self.function.type_of(receiver).clone();
        let table = self.value(receiver);
        let zero = self.builder.ins().iconst(self.pointer, 0);
        self.builder.ins().store(OWNED, zero, table, layout::LENGTH);
        match &held {
            Ty::Builtin {
                kind: Builtin::List,
                ..
            } => {}
            // At zero capacity `find` misses and the next insert allocates.
            Ty::Builtin {
                kind: Builtin::Map | Builtin::Set,
                ..
            } => {
                self.builder
                    .ins()
                    .store(OWNED, zero, table, layout::CAPACITY);
                self.builder.ins().store(OWNED, zero, table, layout::BUFFER);
            }
            _ => self.gap(format!("clearing `{held}`")),
        }
    }

    /// The bucket `key` occupies in the map or set `receiver`, or null.
    fn find_bucket(&mut self, receiver: Value, key: Value) -> Option<ir::Value> {
        let held = self.function.type_of(receiver).clone();
        let Ty::Builtin {
            kind: Builtin::Map | Builtin::FrozenMap | Builtin::Set | Builtin::FrozenSet,
            args,
        } = &held
        else {
            self.gap(format!("looking up `{held}`"));
            return None;
        };
        let text = args
            .first()
            .and_then(|element| self.compared_by_text(element))?;
        let table = self.value(receiver);
        let hash = self.key_hash(key)?;
        let word = self.key_word(key);
        let text = self.builder.ins().iconst(types::I8, i64::from(text));
        let call = self
            .builder
            .ins()
            .call(self.map_find, &[table, word, hash, text]);
        self.builder.inst_results(call).first().copied()
    }

    /// Bucket `index` of the map or set `receiver`, below its bucket count.
    fn bucket_address(&mut self, receiver: Value, index: Value) -> ir::Value {
        let table = self.value(receiver);
        let index = self.value(index);
        let buckets = self
            .builder
            .ins()
            .load(self.pointer, OWNED, table, layout::BUFFER);
        let offset = self.builder.ins().imul_imm(index, layout::BUCKET_BYTES);
        self.builder.ins().iadd(buckets, offset)
    }

    /// The bucket `key` occupies in `map`, claimed where it had none.
    fn map_insert(&mut self, map: ir::Value, key: Value, text: bool) -> Option<ir::Value> {
        let hash = self.key_hash(key)?;
        let word = self.key_word(key);
        let text = self.builder.ins().iconst(types::I8, i64::from(text));
        let call = self
            .builder
            .ins()
            .call(self.map_insert, &[map, word, hash, text]);
        self.builder.inst_results(call).first().copied()
    }

    /// Whether two values of `ty` are the same when their text is rather than
    /// when their words are, or `None` for a type the runtime cannot compare.
    fn compared_by_text(&mut self, ty: &Ty) -> Option<bool> {
        match ty {
            Ty::Str | Ty::Bytes => Some(true),
            Ty::Bool | Ty::Int(_) | Ty::Char => Some(false),
            _ => {
                self.gap(format!("comparing `{ty}`"));
                None
            }
        }
    }

    fn key_hash(&mut self, key: Value) -> Option<ir::Value> {
        let hash = self.hash_value(key)?;
        Some(self.word_of(hash))
    }

    /// A key as the one word a bucket stores it in.
    fn key_word(&mut self, key: Value) -> ir::Value {
        let value = self.value(key);
        self.word_of(value)
    }

    fn word_of(&mut self, value: ir::Value) -> ir::Value {
        let held = self.builder.func.dfg.value_type(value);
        match held.bits().cmp(&self.pointer.bits()) {
            std::cmp::Ordering::Less => self.builder.ins().uextend(self.pointer, value),
            std::cmp::Ordering::Equal => value,
            std::cmp::Ordering::Greater => self.builder.ins().ireduce(self.pointer, value),
        }
    }

    /// Ends the program where it stands, saying which trap it was (LR50).
    fn raise(&mut self, trap: Trap) {
        let handler = self.handlers[handler_index(trap)];
        self.builder.ins().call(handler, &[]);
        self.builder.ins().trap(AFTER_HANDLER);
    }

    /// The same, on a condition, with the rest of the block carrying on.
    fn trap_if(&mut self, condition: ir::Value, trap: Trap) {
        let trapping = self.builder.create_block();
        let carry_on = self.builder.create_block();
        self.builder
            .ins()
            .brif(condition, trapping, &[], carry_on, &[]);

        self.builder.switch_to_block(trapping);
        self.raise(trap);
        self.builder.switch_to_block(carry_on);
    }

    fn value(&mut self, value: Value) -> ir::Value {
        if let Some(found) = self.values.get(&value) {
            return *found;
        }
        // No definition means an earlier gap swallowed the instruction that
        // would have produced it.
        let ty = self.machine_or_gap(value);
        let placeholder = self.builder.ins().iconst(ty, 0);
        self.values.insert(value, placeholder);
        placeholder
    }

    fn machine_or_gap(&mut self, value: Value) -> Type {
        let ty = self.function.type_of(value).clone();
        match machine(&ty, self.pointer) {
            Some(machine) => machine,
            None => {
                self.gap(format!("a value of type `{ty}`"));
                types::I8
            }
        }
    }

    fn gap(&mut self, what: impl Into<String>) {
        self.gaps.push(Gap {
            function: self.function.name.clone(),
            span: self.function.span,
            what: what.into(),
        });
    }
}
