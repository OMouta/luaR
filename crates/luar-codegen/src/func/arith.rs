//! Arithmetic, comparison, and conversion over machine integers.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{self, InstBuilder};
use luar_lir::inst::{BinaryOp, Overflow, Trap, UnaryOp, Value};
use luar_lir::ty::Ty;

use crate::layout::{self, TAG, TAG_TYPE};
use crate::ty::{is_signed, machine};

use super::{OWNED, Translator};

impl Translator<'_, '_> {
    pub(super) fn unary(&mut self, op: UnaryOp, operand: Value) -> Option<ir::Value> {
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

    pub(super) fn binary(&mut self, op: BinaryOp, left: Value, right: Value) -> Option<ir::Value> {
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

    /// LR4.3: the operator applied with the overflow behavior named, where
    /// the ordinary operator would trap.
    pub(super) fn overflowing(
        &mut self,
        mode: Overflow,
        op: BinaryOp,
        left: Value,
        right: Value,
        result: Option<Value>,
    ) -> Option<ir::Value> {
        let signed = is_signed(self.function.type_of(left));
        let a = self.value(left);
        let b = self.value(right);
        let (value, overflow) = match (op, signed) {
            (BinaryOp::Add, true) => self.builder.ins().sadd_overflow(a, b),
            (BinaryOp::Add, false) => self.builder.ins().uadd_overflow(a, b),
            (BinaryOp::Subtract, true) => self.builder.ins().ssub_overflow(a, b),
            (BinaryOp::Subtract, false) => self.builder.ins().usub_overflow(a, b),
            (BinaryOp::Multiply, true) => self.builder.ins().smul_overflow(a, b),
            (BinaryOp::Multiply, false) => self.builder.ins().umul_overflow(a, b),
            _ => {
                self.gap("an overflow-explicit operator");
                return None;
            }
        };

        match mode {
            Overflow::Wrap => Some(value),
            Overflow::Saturate => {
                let width = self.builder.func.dfg.value_type(a);
                let bound = if signed {
                    let bits = width.bits();
                    let (max, min) = if bits == 64 {
                        (i64::MAX, i64::MIN)
                    } else {
                        ((1i64 << (bits - 1)) - 1, -(1i64 << (bits - 1)))
                    };
                    let zero = self.builder.ins().iconst(width, 0);
                    // Which end was left: past the top where the operation
                    // went up, past the bottom where it went down.
                    let upward = match op {
                        BinaryOp::Add => {
                            self.builder
                                .ins()
                                .icmp(IntCC::SignedGreaterThanOrEqual, b, zero)
                        }
                        BinaryOp::Subtract => {
                            self.builder.ins().icmp(IntCC::SignedLessThan, b, zero)
                        }
                        _ => {
                            let product_sign = self.builder.ins().bxor(a, b);
                            self.builder.ins().icmp(
                                IntCC::SignedGreaterThanOrEqual,
                                product_sign,
                                zero,
                            )
                        }
                    };
                    let max = self.builder.ins().iconst(width, max);
                    let min = self.builder.ins().iconst(width, min);
                    self.builder.ins().select(upward, max, min)
                } else {
                    let all_ones = self.builder.ins().iconst(width, -1);
                    let zero = self.builder.ins().iconst(width, 0);
                    match op {
                        BinaryOp::Subtract => zero,
                        _ => all_ones,
                    }
                };
                Some(self.builder.ins().select(overflow, bound, value))
            }
            Overflow::Check => {
                let optional = self.function.type_of(result?).clone();
                let built = self.allocate(&optional, 0)?;
                let present = self.builder.ins().bxor_imm(overflow, 1);
                let tag = self.builder.ins().uextend(TAG_TYPE, present);
                self.builder.ins().store(OWNED, tag, built, TAG);
                self.builder.ins().store(OWNED, value, built, layout::CELL);
                Some(built)
            }
        }
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
    pub(super) fn convert(&mut self, value: Value, to: &Ty) -> Option<ir::Value> {
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
