//! Text: literals, and values shown as text.

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

    pub(super) fn bytes(&mut self, bytes: &[u8]) -> Option<ir::Value> {
        let length = i32::try_from(bytes.len()).unwrap_or(i32::MAX - layout::CELL);
        let built = self.allocate_bytes(layout::CELL.saturating_add(length), &Ty::Bytes, 0)?;
        let length = self.builder.ins().iconst(self.pointer, i64::from(length));
        self.builder.ins().store(OWNED, length, built, 0);
        for (index, byte) in bytes.iter().enumerate() {
            let offset = layout::CELL.saturating_add(i32::try_from(index).unwrap_or(i32::MAX));
            let value = self.builder.ins().iconst(types::I8, i64::from(*byte));
            self.builder.ins().store(OWNED, value, built, offset);
        }
        Some(built)
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
            Ty::Char => {
                let call = self.builder.ins().call(self.display_char, &[value]);
                self.builder.inst_results(call).first().copied()
            }
            _ => {
                self.gap(format!("displaying a value of type `{ty}`"));
                None
            }
        }
    }
}
