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
use luar_lir::ty::{Ty, TypeId};

use crate::Gap;
use crate::layout::{self, TAG, TAG_TYPE};
use crate::ty::machine;

mod arith;
mod calls;
mod list;
mod memory;
mod roots;
mod table;
mod text;

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
    pub display_char: FuncRef,
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
                if !matches!(self.function.type_of(*value), Ty::Dynamic | Ty::Union(_)) {
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
            InstKind::ListPush { receiver, value } => {
                self.list_push(*receiver, *value);
                None
            }
            InstKind::ListPop { receiver } => self.list_pop(*receiver, inst.result),
            InstKind::SetInsert { receiver, value } => {
                self.set_insert(*receiver, *value);
                None
            }
            InstKind::Contains { receiver, value } => self.contains(*receiver, *value),
            InstKind::MapRemove { receiver, key } => self.map_remove(*receiver, *key, inst.result),
            InstKind::SetRemove { receiver, value } => self.set_remove(*receiver, *value),
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
                self.get_index(*receiver, *index, inst.result, true)
            }
            InstKind::GetUncheckedIndex { receiver, index } => {
                self.get_index(*receiver, *index, inst.result, false)
            }
            InstKind::GetCheckedIndex { receiver, index } => {
                self.get_checked_index(*receiver, *index, inst.result)
            }
            InstKind::SetIndex {
                receiver,
                index,
                value,
            } => {
                self.set_index(*receiver, *index, *value, true);
                None
            }
            InstKind::SetUncheckedIndex {
                receiver,
                index,
                value,
            } => {
                self.set_index(*receiver, *index, *value, false);
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
            // LR4.1: `nil` as its own type holds nothing, like `()`.
            Const::Nil if result.is_some_and(|value| *self.function.type_of(value) == Ty::Nil) => {
                self.builder.ins().iconst(types::I8, 0)
            }
            Const::Bool(set) => self.builder.ins().iconst(types::I8, i64::from(*set)),
            // The bits are the bits of the value's own type, and Cranelift
            // reads the width from the type it is given here.
            Const::Int(bits) => self.builder.ins().iconst(ty, *bits as i64),
            Const::Char(scalar) => {
                let scalar = i64::from(u32::from(*scalar));
                self.builder.ins().iconst(types::I32, scalar)
            }
            Const::Str(text) => return self.text(text.as_bytes()),
            Const::Bytes(bytes) => return self.bytes(bytes),
            Const::Nil | Const::Float(_) => {
                self.gap("a literal that is not an integer, a boolean, or a character");
                return None;
            }
        };
        Some(value)
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
