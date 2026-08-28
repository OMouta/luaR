//! One LIR function in Cranelift IR.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    self, AbiParam, Block, FuncRef, GlobalValue, InstBuilder, MemFlags, Signature, StackSlot,
    StackSlotData, StackSlotKind, TrapCode, Type, types,
};
use cranelift_frontend::{FunctionBuilder, Switch};
use luar_lir::inst::{BinaryOp, Const, Inst, InstKind, Terminator, Trap, UnaryOp, Value};
use luar_lir::program::{BlockId, FuncId, Function, Program, SlotId};
use luar_lir::ty::Ty;

use crate::Gap;
use crate::gc::ROOT_FRAME_HEADER;
use crate::layout::{self, TAG, TAG_TYPE};
use crate::ty::{is_signed, machine};

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
    pub abort: FuncRef,
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
            InstKind::MakeStruct { ty, fields } => self.make(ty, 0, fields),
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

            other => {
                self.gap(describe(other));
                None
            }
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

    fn create_slots(&mut self) {
        for (index, ty) in self.function.slots().iter().enumerate() {
            let Some(held) = machine(ty, self.pointer) else {
                self.gap(format!("a slot holding a value of type `{ty}`"));
                continue;
            };
            let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                held.bytes(),
                held.bytes().ilog2() as u8,
            ));
            let id = SlotId(u32::try_from(index).expect("slot count fits in u32"));
            self.slots.insert(id, slot);
        }
    }

    fn prepare_roots(&mut self) {
        let values: Vec<Value> = self
            .function
            .values()
            .filter_map(|(value, ty)| layout::is_aggregate(ty).then_some(value))
            .collect();
        let cell = i32::try_from(self.pointer.bytes()).expect("pointer width fits in i32");
        let temporary_count = usize::try_from(layout::DEPTH).expect("root depth fits in usize");
        let count =
            i32::try_from(values.len().saturating_add(temporary_count)).unwrap_or(i32::MAX / cell);
        let size = cell.saturating_mul(count.saturating_add(ROOT_FRAME_HEADER));
        let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            u32::try_from(size).unwrap_or(u32::MAX),
            self.pointer.bytes().ilog2() as u8,
        ));
        self.root_frame = Some(slot);
        for (index, value) in values.into_iter().enumerate() {
            let offset =
                cell.saturating_mul(i32::try_from(index).unwrap_or(i32::MAX) + ROOT_FRAME_HEADER);
            self.root_offsets.insert(value, offset);
        }
        let first = self.root_offsets.len();
        for index in 0..temporary_count {
            let offset = cell.saturating_mul(
                i32::try_from(first.saturating_add(index)).unwrap_or(i32::MAX) + ROOT_FRAME_HEADER,
            );
            self.temporary_roots.push(offset);
        }
    }

    fn enter_roots(&mut self) {
        let frame = self.builder.ins().stack_addr(
            self.pointer,
            self.root_frame.expect("root frame exists"),
            0,
        );
        let top = self.builder.ins().global_value(self.pointer, self.roots);
        let previous = self.builder.ins().load(self.pointer, OWNED, top, 0);
        self.builder.ins().store(OWNED, previous, frame, 0);

        let cell = i32::try_from(self.pointer.bytes()).expect("pointer width fits in i32");
        let count = self.builder.ins().iconst(
            self.pointer,
            self.root_offsets
                .len()
                .saturating_add(self.temporary_roots.len()) as i64,
        );
        self.builder.ins().store(OWNED, count, frame, cell);
        let name = self
            .builder
            .ins()
            .global_value(self.pointer, self.function_name);
        self.builder
            .ins()
            .store(OWNED, name, frame, cell.saturating_mul(2));
        let name_length = self.builder.ins().iconst(
            self.pointer,
            i64::try_from(self.function_name_length).unwrap_or(0),
        );
        self.builder
            .ins()
            .store(OWNED, name_length, frame, cell.saturating_mul(3));
        let zero = self.builder.ins().iconst(self.pointer, 0);
        for offset in self.root_offsets.values() {
            self.builder.ins().store(OWNED, zero, frame, *offset);
        }
        for offset in &self.temporary_roots {
            self.builder.ins().store(OWNED, zero, frame, *offset);
        }
        self.builder.ins().store(OWNED, frame, top, 0);
    }

    fn leave_roots(&mut self) {
        let frame = self.builder.ins().stack_addr(
            self.pointer,
            self.root_frame.expect("root frame exists"),
            0,
        );
        let previous = self.builder.ins().load(self.pointer, OWNED, frame, 0);
        let top = self.builder.ins().global_value(self.pointer, self.roots);
        self.builder.ins().store(OWNED, previous, top, 0);
    }

    fn root(&mut self, value: Value, machine: ir::Value) {
        let Some(offset) = self.root_offsets.get(&value).copied() else {
            return;
        };
        let frame = self.builder.ins().stack_addr(
            self.pointer,
            self.root_frame.expect("root frame exists"),
            0,
        );
        self.builder.ins().store(OWNED, machine, frame, offset);
    }

    fn root_temporary(&mut self, index: u32, machine: ir::Value) {
        let Some(offset) = self.temporary_roots.get(index as usize).copied() else {
            return;
        };
        let frame = self.builder.ins().stack_addr(
            self.pointer,
            self.root_frame.expect("root frame exists"),
            0,
        );
        self.builder.ins().store(OWNED, machine, frame, offset);
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

    fn unary(&mut self, op: UnaryOp, operand: Value) -> Option<ir::Value> {
        let value = self.value(operand);
        let produced = match op {
            UnaryOp::Negate => self.builder.ins().ineg(value),
            // A `bool` is one byte holding 0 or 1, so flipping the low bit is
            // the whole of `not` (LR4.2).
            UnaryOp::Not => self.builder.ins().bxor_imm(value, 1),
            UnaryOp::BitNot => self.builder.ins().bnot(value),
        };
        Some(produced)
    }

    fn binary(&mut self, op: BinaryOp, left: Value, right: Value) -> Option<ir::Value> {
        let signed = is_signed(self.function.type_of(left));
        let a = self.value(left);
        let b = self.value(right);

        if matches!(self.function.type_of(left), Ty::Str | Ty::Bytes)
            && matches!(op, BinaryOp::Equal | BinaryOp::NotEqual)
        {
            let call = self.builder.ins().call(self.text_equal, &[a, b]);
            let equal = self.builder.inst_results(call).first().copied()?;
            return Some(match op {
                BinaryOp::NotEqual => self.builder.ins().bxor_imm(equal, 1),
                _ => equal,
            });
        }

        // `icmp` already answers the byte holding 0 or 1 that a `bool` is.
        if let Some(condition) = comparison(op, signed) {
            return Some(self.builder.ins().icmp(condition, a, b));
        }

        let produced = match op {
            // LR4.3: an operation that leaves the range of its type traps.
            BinaryOp::Add | BinaryOp::Subtract | BinaryOp::Multiply => {
                return self.checked(op, signed, a, b);
            }
            // LR11.1: `//` and `%` trap on a zero divisor.
            BinaryOp::IntegerDivide | BinaryOp::Remainder => {
                return self.divided(op, signed, a, b);
            }
            BinaryOp::BitAnd => self.builder.ins().band(a, b),
            BinaryOp::BitOr => self.builder.ins().bor(a, b),
            BinaryOp::BitXor => self.builder.ins().bxor(a, b),
            BinaryOp::ShiftLeft => self.builder.ins().ishl(a, b),
            BinaryOp::ShiftRight if signed => self.builder.ins().sshr(a, b),
            BinaryOp::ShiftRight => self.builder.ins().ushr(a, b),
            BinaryOp::Divide => {
                self.gap("`/`");
                return None;
            }
            BinaryOp::Power => return self.power(signed, a, b),
            BinaryOp::Concat => {
                let call = self.builder.ins().call(self.concat, &[a, b]);
                return self.builder.inst_results(call).first().copied();
            }
            _ => unreachable!("every comparison was answered above"),
        };
        Some(produced)
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

    fn assert(&mut self, condition: Value, message: Option<Value>) {
        let condition = self.value(condition);
        let failed = self.builder.ins().icmp_imm(IntCC::Equal, condition, 0);
        let failing = self.builder.create_block();
        let carry_on = self.builder.create_block();
        self.builder.ins().brif(failed, failing, &[], carry_on, &[]);

        self.builder.switch_to_block(failing);
        let message = match message {
            Some(message) => self.value(message),
            None => self.builder.ins().iconst(self.pointer, 0),
        };
        let kind = self.builder.ins().iconst(types::I8, ASSERTION_FAILURE);
        self.builder.ins().call(self.abort, &[kind, message]);
        self.builder.ins().trap(AFTER_HANDLER);
        self.builder.switch_to_block(carry_on);
    }

    /// LR11.1: exponentiation, as repeated multiplication, so LR4.3 decides
    /// what an overflow does. An exponent below zero has no integer answer
    /// and leaves the range of the type.
    fn power(&mut self, signed: bool, base: ir::Value, exponent: ir::Value) -> Option<ir::Value> {
        let width = self.builder.func.dfg.value_type(base);
        if signed {
            let zero = self.builder.ins().iconst(width, 0);
            let below = self
                .builder
                .ins()
                .icmp(IntCC::SignedLessThan, exponent, zero);
            self.trap_if(below, Trap::IntegerOverflow);
        }

        let header = self.builder.create_block();
        let body = self.builder.create_block();
        let done = self.builder.create_block();
        self.builder.append_block_param(header, width);
        self.builder.append_block_param(header, width);
        self.builder.append_block_param(done, width);

        let one = self.builder.ins().iconst(width, 1);
        self.builder.ins().jump(
            header,
            &[ir::BlockArg::Value(one), ir::BlockArg::Value(exponent)],
        );

        self.builder.switch_to_block(header);
        let running = self.builder.block_params(header)[0];
        let left = self.builder.block_params(header)[1];
        let zero = self.builder.ins().iconst(width, 0);
        let more = self.builder.ins().icmp(IntCC::NotEqual, left, zero);
        self.builder
            .ins()
            .brif(more, body, &[], done, &[ir::BlockArg::Value(running)]);

        self.builder.switch_to_block(body);
        let (product, overflow) = if signed {
            self.builder.ins().smul_overflow(running, base)
        } else {
            self.builder.ins().umul_overflow(running, base)
        };
        self.trap_if(overflow, Trap::IntegerOverflow);
        let one = self.builder.ins().iconst(width, 1);
        let next = self.builder.ins().isub(left, one);
        self.builder.ins().jump(
            header,
            &[ir::BlockArg::Value(product), ir::BlockArg::Value(next)],
        );

        self.builder.switch_to_block(done);
        Some(self.builder.block_params(done)[0])
    }

    fn checked(
        &mut self,
        op: BinaryOp,
        signed: bool,
        a: ir::Value,
        b: ir::Value,
    ) -> Option<ir::Value> {
        let (value, overflow) = match (op, signed) {
            (BinaryOp::Add, true) => self.builder.ins().sadd_overflow(a, b),
            (BinaryOp::Add, false) => self.builder.ins().uadd_overflow(a, b),
            (BinaryOp::Subtract, true) => self.builder.ins().ssub_overflow(a, b),
            (BinaryOp::Subtract, false) => self.builder.ins().usub_overflow(a, b),
            (BinaryOp::Multiply, true) => self.builder.ins().smul_overflow(a, b),
            (BinaryOp::Multiply, false) => self.builder.ins().umul_overflow(a, b),
            _ => unreachable!("only the three checked operators reach here"),
        };
        self.trap_if(overflow, Trap::IntegerOverflow);
        Some(value)
    }

    fn divided(
        &mut self,
        op: BinaryOp,
        signed: bool,
        a: ir::Value,
        b: ir::Value,
    ) -> Option<ir::Value> {
        let width = self.builder.func.dfg.value_type(b);
        let zero = self.builder.ins().iconst(width, 0);
        let divides_by_zero = self.builder.ins().icmp(IntCC::Equal, b, zero);
        self.trap_if(divides_by_zero, Trap::DivisionByZero);

        // LR4.3: the one signed quotient that leaves the range of its type.
        if signed {
            let least = self.builder.ins().iconst(width, 1i64 << (width.bits() - 1));
            let minimum = self.builder.ins().icmp(IntCC::Equal, a, least);
            let negative_one = self.builder.ins().iconst(width, -1);
            let inverts = self.builder.ins().icmp(IntCC::Equal, b, negative_one);
            let overflow = self.builder.ins().band(minimum, inverts);
            self.trap_if(overflow, Trap::IntegerOverflow);
        }

        let produced = match (op, signed) {
            (BinaryOp::IntegerDivide, true) => self.builder.ins().sdiv(a, b),
            (BinaryOp::IntegerDivide, false) => self.builder.ins().udiv(a, b),
            (BinaryOp::Remainder, true) => self.builder.ins().srem(a, b),
            (BinaryOp::Remainder, false) => self.builder.ins().urem(a, b),
            _ => unreachable!("only division and remainder reach here"),
        };
        Some(produced)
    }

    /// LR39: a conversion between integer types is written out, and Cranelift
    /// narrows or widens it by what the two widths are.
    fn convert(&mut self, value: Value, to: &Ty) -> Option<ir::Value> {
        let from = self.function.type_of(value).clone();
        let (Some(source), Some(target)) =
            (machine(&from, self.pointer), machine(to, self.pointer))
        else {
            self.gap("a conversion between these types");
            return None;
        };
        let converted = self.value(value);

        if source == target {
            return Some(converted);
        }
        if target.bits() < source.bits() {
            return Some(self.builder.ins().ireduce(target, converted));
        }
        let widened = if is_signed(&from) {
            self.builder.ins().sextend(target, converted)
        } else {
            self.builder.ins().uextend(target, converted)
        };
        Some(widened)
    }

    fn call(&mut self, callee: FuncId, type_args: &[Ty], args: &[Value]) -> Option<ir::Value> {
        if !type_args.is_empty() {
            self.gap("a call monomorphization left generic");
            return None;
        }
        let Some(reference) = self.callees.get(&callee).copied() else {
            self.gap("a call to a function the backend did not emit");
            return None;
        };
        let passed: Vec<ir::Value> = args.iter().map(|arg| self.value(*arg)).collect();
        let call = self.builder.ins().call(reference, &passed);
        match self.builder.inst_results(call).first().copied() {
            Some(result) => Some(result),
            None if self.program.function(callee).result == Ty::Unit => {
                Some(self.builder.ins().iconst(types::I8, 0))
            }
            None => {
                self.gap("a call whose result the ABI did not return");
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

    /// LR31: fresh storage holding what `source` holds. A cell holding a
    /// value struct is copied too, because mutating one through a shared
    /// holder would be observable through the other. A cell holding a
    /// reference keeps referring to the same object.
    fn duplicate(&mut self, source: ir::Value, ty: &Ty, depth: u32) -> Option<ir::Value> {
        let Some(size) = layout::size(self.program, ty, self.pointer) else {
            self.gap(format!("a copy of a value of type `{ty}`"));
            return None;
        };
        if depth == 0 {
            self.gap(format!("a copy of a value nested as deeply as `{ty}`"));
            return None;
        }

        // An enum or an optional holds whichever part its tag says, so which
        // cells to copy is not known here.
        let parts = layout::parts(self.program, ty);
        if parts.is_none() && layout::holds_value_parts(self.program, ty, layout::DEPTH) {
            self.gap(format!("a copy of a value of type `{ty}`"));
            return None;
        }
        let copy = self.allocate(ty, layout::DEPTH - depth)?;
        if let Some(parts) = parts {
            for (index, part) in parts.iter().enumerate() {
                let index = u32::try_from(index).expect("field count fits in u32");
                let Some(offset) = layout::field_offset(self.program, ty, index, self.pointer)
                else {
                    self.gap(format!("a field outside `{ty}`"));
                    return None;
                };
                let Some(machine) = machine(part, self.pointer) else {
                    self.gap(format!("a copy of a field of type `{part}`"));
                    return None;
                };
                let held = self.builder.ins().load(machine, OWNED, source, offset);
                let written = if layout::holds_value_parts(self.program, part, layout::DEPTH) {
                    self.duplicate(held, part, depth - 1).unwrap_or(held)
                } else {
                    held
                };
                self.builder.ins().store(OWNED, written, copy, offset);
            }
        } else {
            for cell in (0..size).step_by(layout::CELL as usize) {
                let held = self.builder.ins().load(TAG_TYPE, OWNED, source, cell);
                self.builder.ins().store(OWNED, held, copy, cell);
            }
        }
        Some(copy)
    }

    /// Storage for an aggregate, with `parts` written into the cells after
    /// `from`.
    fn make(&mut self, ty: &Ty, from: u32, parts: &[Value]) -> Option<ir::Value> {
        let built = self.allocate(ty, 0)?;
        for (index, part) in parts.iter().enumerate() {
            let cell = from + u32::try_from(index).unwrap_or(u32::MAX);
            self.write_at(built, ty, cell, *part);
        }
        Some(built)
    }

    /// Storage large enough for a value of `ty`.
    fn allocate(&mut self, ty: &Ty, temporary: u32) -> Option<ir::Value> {
        let Some(size) = layout::size(self.program, ty, self.pointer) else {
            self.gap(format!("storage for a value of type `{ty}`"));
            return None;
        };
        let size = self.builder.ins().iconst(self.pointer, i64::from(size));
        let finalizer = match self.finalizers.get(ty).copied() {
            Some(function) => self.builder.ins().func_addr(self.pointer, function),
            None => self.builder.ins().iconst(self.pointer, 0),
        };
        let call = self.builder.ins().call(self.allocate, &[size, finalizer]);
        let allocated = self.builder.inst_results(call).first().copied()?;
        self.root_temporary(temporary, allocated);
        Some(allocated)
    }

    /// Reads cell `index` of the aggregate `object` points at.
    fn read(&mut self, object: Value, index: u32, result: Option<Value>) -> Option<ir::Value> {
        let held = self.function.type_of(object).clone();
        let offset = layout::field_offset(self.program, &held, index, self.pointer)?;
        let address = self.value(object);
        let ty = result.map_or(types::I8, |value| self.machine_or_gap(value));
        Some(self.builder.ins().load(ty, OWNED, address, offset))
    }

    fn write(&mut self, object: Value, index: u32, value: Value) {
        let ty = self.function.type_of(object).clone();
        let address = self.value(object);
        self.write_at(address, &ty, index, value);
    }

    fn write_at(&mut self, address: ir::Value, owner: &Ty, index: u32, value: Value) {
        let Some(offset) = layout::field_offset(self.program, owner, index, self.pointer) else {
            self.gap(format!("a field outside `{owner}`"));
            return;
        };
        let written = self.value(value);
        self.builder.ins().store(OWNED, written, address, offset);
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

fn comparison(op: BinaryOp, signed: bool) -> Option<IntCC> {
    let condition = match op {
        BinaryOp::Equal => IntCC::Equal,
        BinaryOp::NotEqual => IntCC::NotEqual,
        BinaryOp::Less if signed => IntCC::SignedLessThan,
        BinaryOp::Less => IntCC::UnsignedLessThan,
        BinaryOp::LessEqual if signed => IntCC::SignedLessThanOrEqual,
        BinaryOp::LessEqual => IntCC::UnsignedLessThanOrEqual,
        BinaryOp::Greater if signed => IntCC::SignedGreaterThan,
        BinaryOp::Greater => IntCC::UnsignedGreaterThan,
        BinaryOp::GreaterEqual if signed => IntCC::SignedGreaterThanOrEqual,
        BinaryOp::GreaterEqual => IntCC::UnsignedGreaterThanOrEqual,
        _ => return None,
    };
    Some(condition)
}

fn describe(kind: &InstKind) -> &'static str {
    match kind {
        InstKind::IsType { .. } => "a type test",
        InstKind::CallIndirect { .. } => "a call through a value",
        InstKind::CallVirtual { .. } => "a call through an interface",
        InstKind::MakeDyn { .. } | InstKind::DynValue { .. } => "a dynamic value",
        InstKind::MakeClosure { .. } => "a closure",
        InstKind::MakeStruct { .. } | InstKind::GetField { .. } | InstKind::SetField { .. } => {
            "a struct"
        }
        InstKind::MakeEnum { .. } | InstKind::GetTag { .. } | InstKind::GetPayload { .. } => {
            "an enum"
        }
        InstKind::MakeTuple(_) | InstKind::GetElement { .. } => "a tuple",
        InstKind::MakeList { .. } | InstKind::MakeMap { .. } | InstKind::MakeSet { .. } => {
            "a collection"
        }
        InstKind::GetIndex { .. } | InstKind::SetIndex { .. } => "an indexing operation",
        InstKind::MakeSome { .. } | InstKind::IsSome { .. } | InstKind::Unwrap { .. } => {
            "an optional"
        }
        _ => "this instruction",
    }
}
