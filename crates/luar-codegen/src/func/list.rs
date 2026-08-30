//! Lists (LR13.1) and the indexing that reaches into them and into maps.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{self, InstBuilder, Type, types};
use luar_lir::inst::{Trap, Value};
use luar_lir::ty::{Builtin, Ty};

use crate::layout::{self, TAG, TAG_TYPE};
use crate::ty::machine;

use super::{OWNED, Translator};

impl Translator<'_, '_> {
    pub(super) fn make_slice(
        &mut self,
        receiver: Value,
        range: Value,
        inclusive: bool,
        result: Option<Value>,
    ) -> Option<ir::Value> {
        let ty = self.function.type_of(result?).clone();
        let source_ty = self.function.type_of(receiver).clone();
        let (source, start, end, outside, zero) = self.slice_bounds(receiver, range, inclusive);
        self.trap_if(outside, Trap::Bounds);
        self.slice_value(&ty, &source_ty, source, start, end, zero)
    }

    pub(super) fn make_checked_slice(
        &mut self,
        receiver: Value,
        range: Value,
        inclusive: bool,
        result: Option<Value>,
    ) -> Option<ir::Value> {
        let optional = self.function.type_of(result?).clone();
        let Ty::Optional(slice_ty) = &optional else {
            self.gap("a checked slice that is not optional");
            return None;
        };
        let slice_ty = slice_ty.as_ref().clone();
        let source_ty = self.function.type_of(receiver).clone();
        let (source, start, end, outside, zero) = self.slice_bounds(receiver, range, inclusive);
        let valid = self.builder.ins().icmp_imm(IntCC::Equal, outside, 0);
        let present = self.builder.create_block();
        let absent = self.builder.create_block();
        let join = self.builder.create_block();
        self.builder.append_block_param(join, self.pointer);
        self.builder.ins().brif(valid, present, &[], absent, &[]);

        self.builder.switch_to_block(present);
        let slice = self.slice_value(&slice_ty, &source_ty, source, start, end, zero)?;
        let some = self.allocate(&optional, 0)?;
        let one = self.builder.ins().iconst(layout::TAG_TYPE, 1);
        self.builder.ins().store(OWNED, one, some, layout::TAG);
        self.builder.ins().store(OWNED, slice, some, layout::CELL);
        self.builder.ins().jump(join, &[ir::BlockArg::Value(some)]);

        self.builder.switch_to_block(absent);
        let none = self.allocate(&optional, 0)?;
        self.builder.ins().store(OWNED, zero, none, layout::TAG);
        self.builder.ins().jump(join, &[ir::BlockArg::Value(none)]);

        self.builder.switch_to_block(join);
        Some(self.builder.block_params(join)[0])
    }

    fn slice_bounds(
        &mut self,
        receiver: Value,
        range: Value,
        inclusive: bool,
    ) -> (ir::Value, ir::Value, ir::Value, ir::Value, ir::Value) {
        let source = self.value(receiver);
        let range = self.value(range);
        let length = self
            .builder
            .ins()
            .load(self.pointer, OWNED, source, layout::LENGTH);

        let start_optional = self.builder.ins().load(self.pointer, OWNED, range, 0);
        let start_tag =
            self.builder
                .ins()
                .load(layout::TAG_TYPE, OWNED, start_optional, layout::TAG);
        let start_value =
            self.builder
                .ins()
                .load(self.pointer, OWNED, start_optional, layout::CELL);
        let zero = self.builder.ins().iconst(self.pointer, 0);
        let has_start = self.builder.ins().icmp_imm(IntCC::NotEqual, start_tag, 0);
        let start = self.builder.ins().select(has_start, start_value, zero);

        let end_optional = self
            .builder
            .ins()
            .load(self.pointer, OWNED, range, layout::CELL);
        let end_tag = self
            .builder
            .ins()
            .load(layout::TAG_TYPE, OWNED, end_optional, layout::TAG);
        let end_value = self
            .builder
            .ins()
            .load(self.pointer, OWNED, end_optional, layout::CELL);
        let has_end = self.builder.ins().icmp_imm(IntCC::NotEqual, end_tag, 0);
        let written_end = if inclusive {
            self.builder.ins().iadd_imm(end_value, 1)
        } else {
            end_value
        };
        let end = self.builder.ins().select(has_end, written_end, length);

        let start_outside = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedGreaterThan, start, length);
        let end_outside = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedGreaterThan, end, length);
        let reversed = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedGreaterThan, start, end);
        let outside = self.builder.ins().bor(start_outside, end_outside);
        let outside = self.builder.ins().bor(outside, reversed);

        (source, start, end, outside, zero)
    }

    fn slice_value(
        &mut self,
        ty: &Ty,
        source_ty: &Ty,
        source: ir::Value,
        start: ir::Value,
        end: ir::Value,
        zero: ir::Value,
    ) -> Option<ir::Value> {
        let slice_length = self.builder.ins().isub(end, start);
        let (owner, source_start) = if matches!(
            source_ty,
            Ty::Builtin {
                kind: Builtin::Slice,
                ..
            }
        ) {
            let owner = self
                .builder
                .ins()
                .load(self.pointer, OWNED, source, layout::BUFFER);
            let source_start =
                self.builder
                    .ins()
                    .load(self.pointer, OWNED, source, layout::CAPACITY);
            (owner, source_start)
        } else {
            (source, zero)
        };
        let absolute_start = self.builder.ins().iadd(source_start, start);
        let borrows = self
            .builder
            .ins()
            .load(self.pointer, OWNED, owner, layout::BORROWS);
        let borrowed = self.builder.ins().iadd_imm(borrows, 1);
        self.builder
            .ins()
            .store(OWNED, borrowed, owner, layout::BORROWS);
        let slice = self.allocate(ty, 0)?;
        self.builder
            .ins()
            .store(OWNED, slice_length, slice, layout::LENGTH);
        self.builder
            .ins()
            .store(OWNED, absolute_start, slice, layout::CAPACITY);
        self.builder
            .ins()
            .store(OWNED, owner, slice, layout::BUFFER);
        self.builder
            .ins()
            .store(OWNED, zero, slice, layout::BORROWS);
        Some(slice)
    }

    /// LR13.1: a list is its header, and then storage holding one cell per
    /// element.
    pub(super) fn make_list(
        &mut self,
        result: Option<Value>,
        values: &[Value],
    ) -> Option<ir::Value> {
        let ty = self.function.type_of(result?).clone();
        if matches!(ty, Ty::Array(..)) {
            let built = self.allocate(&ty, 0)?;
            for (index, value) in values.iter().enumerate() {
                let index = u32::try_from(index).unwrap_or(u32::MAX);
                self.write_at(built, &ty, index, *value);
            }
            return Some(built);
        }
        let header = self.allocate(&ty, 0)?;
        let cells = i32::try_from(values.len()).unwrap_or(i32::MAX / layout::CELL);
        let buffer = self.allocate_bytes((layout::CELL * cells).max(layout::CELL), &ty, 1)?;
        for (index, value) in values.iter().enumerate() {
            let written = self.value(*value);
            let offset = layout::CELL * i32::try_from(index).unwrap_or(i32::MAX / layout::CELL);
            self.builder.ins().store(OWNED, written, buffer, offset);
        }
        let length = self.builder.ins().iconst(self.pointer, i64::from(cells));
        self.builder
            .ins()
            .store(OWNED, length, header, layout::LENGTH);
        self.builder
            .ins()
            .store(OWNED, length, header, layout::CAPACITY);
        self.builder
            .ins()
            .store(OWNED, buffer, header, layout::BUFFER);
        let zero = self.builder.ins().iconst(self.pointer, 0);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::BORROWS);
        Some(header)
    }

    pub(super) fn get_index(
        &mut self,
        receiver: Value,
        index: Value,
        result: Option<Value>,
        checked: bool,
    ) -> Option<ir::Value> {
        let held = self.function.type_of(receiver).clone();
        match &held {
            Ty::Builtin {
                kind: Builtin::List | Builtin::FrozenList | Builtin::Slice,
                ..
            } => {
                let address = self.element_address(receiver, index, checked);
                let ty = result.map_or(types::I8, |value| self.machine_or_gap(value));
                Some(self.builder.ins().load(ty, OWNED, address, 0))
            }
            Ty::Builtin {
                kind: Builtin::Map | Builtin::FrozenMap,
                args,
            } => {
                let text = self.compared_by_text(args.first()?)?;
                let map = self.value(receiver);
                let hash = self.key_hash(index)?;
                let word = self.key_word(index);
                let text = self.builder.ins().iconst(types::I8, i64::from(text));
                let call = self
                    .builder
                    .ins()
                    .call(self.map_find, &[map, word, hash, text]);
                let bucket = self.builder.inst_results(call).first().copied()?;

                // LR69: what the map holds at the key, or nothing.
                let optional = self.function.type_of(result?).clone();
                let Ty::Optional(inner) = &optional else {
                    self.gap("a map lookup that is not optional");
                    return None;
                };
                let Some(machine) = machine(inner, self.pointer) else {
                    self.gap(format!("a map holding `{inner}`"));
                    return None;
                };
                let built = self.allocate(&optional, 0)?;
                let present = self.builder.ins().icmp_imm(IntCC::NotEqual, bucket, 0);
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
                self.builder.ins().jump(carry_on, &[]);
                self.builder.switch_to_block(carry_on);
                Some(built)
            }
            Ty::Array(_, length) => {
                let address = self.array_address(receiver, index, *length, checked);
                let ty = result.map_or(types::I8, |value| self.machine_or_gap(value));
                Some(self.builder.ins().load(ty, OWNED, address, 0))
            }
            Ty::Bytes => {
                let address = self.byte_address(receiver, index, checked);
                Some(self.builder.ins().load(types::I8, OWNED, address, 0))
            }
            _ => {
                self.gap(format!("indexing a value of type `{held}`"));
                None
            }
        }
    }

    pub(super) fn get_checked_index(
        &mut self,
        receiver: Value,
        index: Value,
        result: Option<Value>,
    ) -> Option<ir::Value> {
        let held = self.function.type_of(receiver).clone();
        if matches!(
            held,
            Ty::Builtin {
                kind: Builtin::Map | Builtin::FrozenMap,
                ..
            }
        ) {
            return self.get_index(receiver, index, result, true);
        }
        if !matches!(
            held,
            Ty::Builtin {
                kind: Builtin::List | Builtin::FrozenList,
                ..
            }
        ) {
            self.gap(format!("a checked lookup on `{held}`"));
            return None;
        }

        let optional = self.function.type_of(result?).clone();
        let Ty::Optional(inner) = &optional else {
            self.gap("a checked list lookup that is not optional");
            return None;
        };
        let Some(machine) = machine(inner, self.pointer) else {
            self.gap(format!("a list holding `{inner}`"));
            return None;
        };
        let list = self.value(receiver);
        let index = self.value(index);
        let length = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::LENGTH);
        let present = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, index, length);
        let built = self.allocate(&optional, 0)?;
        let tag = self.builder.ins().uextend(TAG_TYPE, present);
        self.builder.ins().store(OWNED, tag, built, TAG);

        let found = self.builder.create_block();
        let carry_on = self.builder.create_block();
        self.builder.ins().brif(present, found, &[], carry_on, &[]);
        self.builder.switch_to_block(found);
        let buffer = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BUFFER);
        let offset = self.builder.ins().imul_imm(index, i64::from(layout::CELL));
        let address = self.builder.ins().iadd(buffer, offset);
        let value = self.builder.ins().load(machine, OWNED, address, 0);
        self.builder.ins().store(OWNED, value, built, layout::CELL);
        self.builder.ins().jump(carry_on, &[]);
        self.builder.switch_to_block(carry_on);
        Some(built)
    }

    /// The machine type of what the mutable list `receiver` holds.
    fn mutable_list_element(&mut self, receiver: Value) -> Option<Type> {
        let held = self.function.type_of(receiver).clone();
        let Ty::Builtin {
            kind: Builtin::List,
            args,
        } = &held
        else {
            self.gap(format!("mutating `{held}`"));
            return None;
        };
        let Some(element) = args.first() else {
            self.gap("a list without an element type");
            return None;
        };
        let Some(machine) = machine(element, self.pointer) else {
            self.gap(format!("a list holding `{element}`"));
            return None;
        };
        Some(machine)
    }

    fn list_cell(&mut self, buffer: ir::Value, index: ir::Value) -> ir::Value {
        let offset = self.builder.ins().imul_imm(index, i64::from(layout::CELL));
        self.builder.ins().iadd(buffer, offset)
    }

    pub(super) fn check_unborrowed(&mut self, list: ir::Value) {
        let borrows = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BORROWS);
        let borrowed = self.builder.ins().icmp_imm(IntCC::NotEqual, borrows, 0);
        let collect = self.builder.create_block();
        let ready = self.builder.create_block();
        self.builder.ins().brif(borrowed, collect, &[], ready, &[]);

        self.builder.switch_to_block(collect);
        self.builder.ins().call(self.collect, &[]);
        let borrows = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BORROWS);
        let borrowed = self.builder.ins().icmp_imm(IntCC::NotEqual, borrows, 0);
        self.trap_if(borrowed, Trap::BorrowedMutation);
        self.builder.ins().jump(ready, &[]);

        self.builder.switch_to_block(ready);
    }

    pub(super) fn list_push(&mut self, receiver: Value, value: Value) {
        let Some(machine) = self.mutable_list_element(receiver) else {
            return;
        };
        let list = self.value(receiver);
        self.check_unborrowed(list);
        let length = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::LENGTH);
        let needed = self.builder.ins().iadd_imm(length, 1);
        self.list_reserve(list, length, needed, machine);
        let buffer = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BUFFER);
        let cell = self.list_cell(buffer, length);
        let written = self.value(value);
        self.builder.ins().store(OWNED, written, cell, 0);
        let length = self.builder.ins().iadd_imm(length, 1);
        self.builder
            .ins()
            .store(OWNED, length, list, layout::LENGTH);
    }

    /// Room for one more element past `length`: a full buffer is doubled
    /// first. Continues in a block where `BUFFER` has to be read again.
    fn list_reserve(
        &mut self,
        list: ir::Value,
        length: ir::Value,
        needed: ir::Value,
        machine: Type,
    ) {
        let capacity = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::CAPACITY);
        let full = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, capacity, needed);
        let grow = self.builder.create_block();
        let copy = self.builder.create_block();
        let copy_one = self.builder.create_block();
        let swap = self.builder.create_block();
        let ready = self.builder.create_block();
        self.builder.append_block_param(copy, self.pointer);
        self.builder.ins().brif(full, grow, &[], ready, &[]);

        self.builder.switch_to_block(grow);
        let doubled = self.builder.ins().imul_imm(capacity, 2);
        let least = self.builder.ins().iconst(self.pointer, 4);
        let small = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, doubled, least);
        let grown = self.builder.ins().select(small, least, doubled);
        let short = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, grown, needed);
        let grown = self.builder.ins().select(short, needed, grown);
        let bytes = self.builder.ins().imul_imm(grown, i64::from(layout::CELL));
        let no_finalizer = self.builder.ins().iconst(self.pointer, 0);
        let call = self
            .builder
            .ins()
            .call(self.allocate, &[bytes, no_finalizer]);
        let fresh = self.builder.inst_results(call)[0];
        let zero = self.builder.ins().iconst(self.pointer, 0);
        self.builder.ins().jump(copy, &[ir::BlockArg::Value(zero)]);

        self.builder.switch_to_block(copy);
        let index = self.builder.block_params(copy)[0];
        let more = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, index, length);
        self.builder.ins().brif(more, copy_one, &[], swap, &[]);

        self.builder.switch_to_block(copy_one);
        let old = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BUFFER);
        let old_cell = self.list_cell(old, index);
        let new_cell = self.list_cell(fresh, index);
        let copied = self.builder.ins().load(machine, OWNED, old_cell, 0);
        self.builder.ins().store(OWNED, copied, new_cell, 0);
        let following = self.builder.ins().iadd_imm(index, 1);
        self.builder
            .ins()
            .jump(copy, &[ir::BlockArg::Value(following)]);

        self.builder.switch_to_block(swap);
        self.builder.ins().store(OWNED, fresh, list, layout::BUFFER);
        self.builder
            .ins()
            .store(OWNED, grown, list, layout::CAPACITY);
        self.builder.ins().jump(ready, &[]);

        self.builder.switch_to_block(ready);
    }

    pub(super) fn list_pop(&mut self, receiver: Value, result: Option<Value>) -> Option<ir::Value> {
        let optional = self.function.type_of(result?).clone();
        let Ty::Optional(inner) = &optional else {
            self.gap("a pop that is not optional");
            return None;
        };
        let Some(machine) = machine(inner, self.pointer) else {
            self.gap(format!("a list holding `{inner}`"));
            return None;
        };
        let list = self.value(receiver);
        self.check_unborrowed(list);
        let length = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::LENGTH);
        let present = self.builder.ins().icmp_imm(IntCC::NotEqual, length, 0);
        let built = self.allocate(&optional, 0)?;
        let tag = self.builder.ins().uextend(TAG_TYPE, present);
        self.builder.ins().store(OWNED, tag, built, TAG);

        let found = self.builder.create_block();
        let carry_on = self.builder.create_block();
        self.builder.ins().brif(present, found, &[], carry_on, &[]);
        self.builder.switch_to_block(found);
        let last = self.builder.ins().iadd_imm(length, -1);
        self.builder.ins().store(OWNED, last, list, layout::LENGTH);
        let buffer = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BUFFER);
        let offset = self.builder.ins().imul_imm(last, i64::from(layout::CELL));
        let address = self.builder.ins().iadd(buffer, offset);
        let value = self.builder.ins().load(machine, OWNED, address, 0);
        self.builder.ins().store(OWNED, value, built, layout::CELL);
        self.builder.ins().jump(carry_on, &[]);
        self.builder.switch_to_block(carry_on);
        Some(built)
    }

    pub(super) fn contains(&mut self, receiver: Value, value: Value) -> Option<ir::Value> {
        let bucket = self.find_bucket(receiver, value)?;
        Some(self.builder.ins().icmp_imm(IntCC::NotEqual, bucket, 0))
    }

    pub(super) fn set_index(&mut self, receiver: Value, index: Value, value: Value, checked: bool) {
        let held = self.function.type_of(receiver).clone();
        match &held {
            Ty::Builtin {
                kind: Builtin::List,
                ..
            } => {
                let list = self.value(receiver);
                self.check_unborrowed(list);
                let address = self.element_address(receiver, index, checked);
                let written = self.value(value);
                self.builder.ins().store(OWNED, written, address, 0);
            }
            Ty::Builtin {
                kind: Builtin::Slice,
                ..
            } => {
                let address = self.element_address(receiver, index, checked);
                let written = self.value(value);
                self.builder.ins().store(OWNED, written, address, 0);
            }
            Ty::Builtin {
                kind: Builtin::Map,
                args,
            } => {
                let Some(text) = args.first().and_then(|key| self.compared_by_text(key)) else {
                    return;
                };
                let map = self.value(receiver);
                if let Some(bucket) = self.map_insert(map, index, text) {
                    let written = self.value(value);
                    self.builder
                        .ins()
                        .store(OWNED, written, bucket, layout::BUCKET_VALUE);
                }
            }
            Ty::Array(_, length) => {
                let address = self.array_address(receiver, index, *length, checked);
                let written = self.value(value);
                self.builder.ins().store(OWNED, written, address, 0);
            }
            Ty::Bytes => {
                let address = self.byte_address(receiver, index, checked);
                let written = self.value(value);
                self.builder.ins().store(OWNED, written, address, 0);
            }
            _ => self.gap(format!("indexing a value of type `{held}`")),
        }
    }

    fn byte_address(&mut self, receiver: Value, index: Value, checked: bool) -> ir::Value {
        let bytes = self.value(receiver);
        let index = self.value(index);
        if checked {
            let length = self
                .builder
                .ins()
                .load(self.pointer, OWNED, bytes, layout::LENGTH);
            let outside = self
                .builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThanOrEqual, index, length);
            self.trap_if(outside, Trap::Bounds);
        }
        let start = self.builder.ins().iadd_imm(bytes, i64::from(layout::CELL));
        self.builder.ins().iadd(start, index)
    }

    fn array_address(
        &mut self,
        receiver: Value,
        index: Value,
        length: u64,
        checked: bool,
    ) -> ir::Value {
        let array = self.value(receiver);
        let index = self.value(index);
        if checked {
            let length = self.builder.ins().iconst(self.pointer, length as i64);
            let outside = self
                .builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThanOrEqual, index, length);
            self.trap_if(outside, Trap::Bounds);
        }
        let offset = self.builder.ins().imul_imm(index, i64::from(layout::CELL));
        self.builder.ins().iadd(array, offset)
    }

    /// LR70: the cell of element `index`, with a bounds check when requested.
    fn element_address(&mut self, receiver: Value, index: Value, checked: bool) -> ir::Value {
        let held = self.function.type_of(receiver).clone();
        let collection = self.value(receiver);
        let index = self.value(index);
        if checked {
            let length = self
                .builder
                .ins()
                .load(self.pointer, OWNED, collection, layout::LENGTH);
            let outside = self
                .builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThanOrEqual, index, length);
            self.trap_if(outside, Trap::Bounds);
        }
        let (list, index) = if matches!(
            held,
            Ty::Builtin {
                kind: Builtin::Slice,
                ..
            }
        ) {
            let list = self
                .builder
                .ins()
                .load(self.pointer, OWNED, collection, layout::BUFFER);
            let start = self
                .builder
                .ins()
                .load(self.pointer, OWNED, collection, layout::CAPACITY);
            (list, self.builder.ins().iadd(start, index))
        } else {
            (collection, index)
        };
        let buffer = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BUFFER);
        let offset = self.builder.ins().imul_imm(index, i64::from(layout::CELL));
        self.builder.ins().iadd(buffer, offset)
    }
}
