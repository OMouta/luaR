//! Text: literals, strings built at runtime, and values shown as text.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{self, InstBuilder, types};
use luar_lir::inst::Value;
use luar_lir::ty::Ty;

use crate::layout;

use super::{OWNED, Translator};

impl Translator<'_, '_> {
    /// The address of a literal's text, which lives in the object rather than
    /// being built at runtime (LR4.5).
    pub(super) fn text(&mut self, bytes: &[u8]) -> Option<ir::Value> {
        let Some(&data) = self.texts.get(bytes) else {
            self.gap("a literal the object has no text for");
            return None;
        };
        Some(self.builder.ins().global_value(self.pointer, data))
    }

    /// LR72: a string holding `length` bytes copied from `data`.
    pub(super) fn make_text(&mut self, data: Value, length: Value) -> Option<ir::Value> {
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

    pub(super) fn display_value(&mut self, value: Value) -> Option<ir::Value> {
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
}
