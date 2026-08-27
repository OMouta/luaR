//! One LIR function in Cranelift IR.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    self, AbiParam, Block, FuncRef, InstBuilder, Signature, TrapCode, Type, types,
};
use cranelift_frontend::{FunctionBuilder, Switch};
use luar_lir::inst::{BinaryOp, Const, Inst, InstKind, Terminator, Trap, UnaryOp, Value};
use luar_lir::program::{BlockId, FuncId, Function};
use luar_lir::ty::Ty;

use crate::Gap;
use crate::ty::{is_signed, machine};

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
    signature
        .returns
        .push(AbiParam::new(machine(&function.result, pointer)?));
    Some(signature)
}

pub(crate) struct Translator<'a, 'b> {
    pub function: &'a Function,
    pub builder: FunctionBuilder<'b>,
    pub pointer: Type,
    pub callees: HashMap<FuncId, FuncRef>,
    /// The runtime handler for each trap kind, in [`TRAPS`] order.
    pub handlers: [FuncRef; TRAPS.len()],
    pub blocks: HashMap<BlockId, Block>,
    pub values: HashMap<Value, ir::Value>,
    pub gaps: Vec<Gap>,
}

impl Translator<'_, '_> {
    /// Walks every block, in the order the function holds them, and gives
    /// back what it could not emit.
    pub fn run(mut self) -> Vec<Gap> {
        self.create_blocks();

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
                let value = self.value(*value);
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
            InstKind::Convert { value, to } => self.convert(*value, to),
            InstKind::Call {
                callee,
                type_args,
                args,
            } => self.call(*callee, type_args, args),
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
    }

    fn constant(&mut self, literal: &Const, result: Option<Value>) -> Option<ir::Value> {
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
            Const::Nil | Const::Float(_) | Const::Str(_) | Const::Bytes(_) => {
                self.gap("a literal the backend cannot emit yet");
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
            BinaryOp::Divide | BinaryOp::Power | BinaryOp::Concat => {
                self.gap("an operator the backend cannot emit yet");
                return None;
            }
            _ => unreachable!("every comparison was answered above"),
        };
        Some(produced)
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
            self.gap("a conversion the backend cannot emit yet");
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
        self.builder.inst_results(call).first().copied()
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
        InstKind::AddressOf { .. } | InstKind::Load { .. } | InstKind::Store { .. } => "a pointer",
        InstKind::SlotGet { .. } | InstKind::SlotSet { .. } => "a stack slot",
        _ => "an instruction the backend cannot emit yet",
    }
}
