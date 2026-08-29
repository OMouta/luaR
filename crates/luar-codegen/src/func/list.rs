//! Lists (LR13.1) and the indexing that reaches into them and into maps.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{self, InstBuilder, Type, types};
use luar_lir::inst::{Trap, Value};
use luar_lir::ty::{Builtin, Ty};

use crate::layout::{self, TAG, TAG_TYPE};
use crate::ty::machine;

use super::{OWNED, Translator};

impl Translator<'_, '_> {
    /// LR13.1: a list is its header, and then storage holding one cell per
    /// element.
    pub(super) fn make_list(
        &mut self,
        result: Option<Value>,
        values: &[Value],
    ) -> Option<ir::Value> {
        let ty = self.function.type_of(result?).clone();
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
        Some(header)
    }

    pub(super) fn get_index(
        &mut self,
        receiver: Value,
        index: Value,
        result: Option<Value>,
    ) -> Option<ir::Value> {
        let held = self.function.type_of(receiver).clone();
        match &held {
            Ty::Builtin {
                kind: Builtin::List | Builtin::FrozenList,
                ..
            } => {
                let address = self.element_address(receiver, index);
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
            return self.get_index(receiver, index, result);
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

    pub(super) fn list_push(&mut self, receiver: Value, value: Value) {
        let Some(machine) = self.mutable_list_element(receiver) else {
            return;
        };
        let list = self.value(receiver);
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

    pub(super) fn list_push_all(&mut self, receiver: Value, other: Value) {
        let Some(machine) = self.mutable_list_element(receiver) else {
            return;
        };
        let list = self.value(receiver);
        let source = self.value(other);
        let length = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::LENGTH);
        let added = self
            .builder
            .ins()
            .load(self.pointer, OWNED, source, layout::LENGTH);
        let total = self.builder.ins().iadd(length, added);
        self.list_reserve(list, length, total, machine);
        // Loaded after reserving, so a list pushed onto itself reads the
        // buffer it now holds.
        let buffer = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BUFFER);
        let from = self
            .builder
            .ins()
            .load(self.pointer, OWNED, source, layout::BUFFER);
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
            .icmp(IntCC::UnsignedLessThan, index, added);
        self.builder
            .ins()
            .brif(more, copy_one, &[ir::BlockArg::Value(index)], done, &[]);

        self.builder.switch_to_block(copy_one);
        let index = self.builder.block_params(copy_one)[0];
        let at = self.builder.ins().iadd(length, index);
        let source_cell = self.list_cell(from, index);
        let cell = self.list_cell(buffer, at);
        let copied = self.builder.ins().load(machine, OWNED, source_cell, 0);
        self.builder.ins().store(OWNED, copied, cell, 0);
        let following = self.builder.ins().iadd_imm(index, 1);
        self.builder
            .ins()
            .jump(copy, &[ir::BlockArg::Value(following)]);

        self.builder.switch_to_block(done);
        self.builder.ins().store(OWNED, total, list, layout::LENGTH);
    }

    pub(super) fn list_insert(&mut self, receiver: Value, index: Value, value: Value) {
        let Some(machine) = self.mutable_list_element(receiver) else {
            return;
        };
        let list = self.value(receiver);
        let index = self.value(index);
        let length = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::LENGTH);
        let past = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedGreaterThan, index, length);
        self.trap_if(past, Trap::Bounds);
        let needed = self.builder.ins().iadd_imm(length, 1);
        self.list_reserve(list, length, needed, machine);
        let buffer = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BUFFER);

        // Each element from the end down to `index` moves up one cell.
        let shift = self.builder.create_block();
        let shift_one = self.builder.create_block();
        let write = self.builder.create_block();
        self.builder.append_block_param(shift, self.pointer);
        self.builder
            .ins()
            .jump(shift, &[ir::BlockArg::Value(length)]);

        self.builder.switch_to_block(shift);
        let cursor = self.builder.block_params(shift)[0];
        let more = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedGreaterThan, cursor, index);
        self.builder.ins().brif(more, shift_one, &[], write, &[]);

        self.builder.switch_to_block(shift_one);
        let before = self.builder.ins().iadd_imm(cursor, -1);
        let from = self.list_cell(buffer, before);
        let to = self.list_cell(buffer, cursor);
        let moved = self.builder.ins().load(machine, OWNED, from, 0);
        self.builder.ins().store(OWNED, moved, to, 0);
        self.builder
            .ins()
            .jump(shift, &[ir::BlockArg::Value(before)]);

        self.builder.switch_to_block(write);
        let cell = self.list_cell(buffer, index);
        let written = self.value(value);
        self.builder.ins().store(OWNED, written, cell, 0);
        let length = self.builder.ins().iadd_imm(length, 1);
        self.builder
            .ins()
            .store(OWNED, length, list, layout::LENGTH);
    }

    pub(super) fn list_remove_at(&mut self, receiver: Value, index: Value) -> Option<ir::Value> {
        let machine = self.mutable_list_element(receiver)?;
        let address = self.element_address(receiver, index);
        let removed = self.builder.ins().load(machine, OWNED, address, 0);
        let list = self.value(receiver);
        let index = self.value(index);
        let length = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::LENGTH);
        let last = self.builder.ins().iadd_imm(length, -1);
        let buffer = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BUFFER);

        // Each element after `index` moves down one cell.
        let shift = self.builder.create_block();
        let shift_one = self.builder.create_block();
        let done = self.builder.create_block();
        self.builder.append_block_param(shift, self.pointer);
        self.builder
            .ins()
            .jump(shift, &[ir::BlockArg::Value(index)]);

        self.builder.switch_to_block(shift);
        let cursor = self.builder.block_params(shift)[0];
        let more = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, cursor, last);
        self.builder.ins().brif(more, shift_one, &[], done, &[]);

        self.builder.switch_to_block(shift_one);
        let after = self.builder.ins().iadd_imm(cursor, 1);
        let from = self.list_cell(buffer, after);
        let to = self.list_cell(buffer, cursor);
        let moved = self.builder.ins().load(machine, OWNED, from, 0);
        self.builder.ins().store(OWNED, moved, to, 0);
        self.builder
            .ins()
            .jump(shift, &[ir::BlockArg::Value(after)]);

        self.builder.switch_to_block(done);
        self.builder.ins().store(OWNED, last, list, layout::LENGTH);
        Some(removed)
    }

    /// Room for one more element past `length`: a full buffer is doubled
    /// first. Continues in a block where `BUFFER` has to be read again.
    pub(super) fn list_reverse(&mut self, receiver: Value) {
        let Some(machine) = self.mutable_list_element(receiver) else {
            return;
        };
        let list = self.value(receiver);
        let length = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::LENGTH);
        let buffer = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BUFFER);
        let scan = self.builder.create_block();
        let swap = self.builder.create_block();
        let done = self.builder.create_block();
        self.builder.append_block_param(scan, self.pointer);
        self.builder.append_block_param(scan, self.pointer);
        self.builder.append_block_param(swap, self.pointer);
        self.builder.append_block_param(swap, self.pointer);
        let zero = self.builder.ins().iconst(self.pointer, 0);
        let last = self.builder.ins().iadd_imm(length, -1);
        self.builder.ins().jump(
            scan,
            &[ir::BlockArg::Value(zero), ir::BlockArg::Value(last)],
        );

        self.builder.switch_to_block(scan);
        let low = self.builder.block_params(scan)[0];
        let high = self.builder.block_params(scan)[1];
        let more = self.builder.ins().icmp(IntCC::SignedLessThan, low, high);
        self.builder.ins().brif(
            more,
            swap,
            &[ir::BlockArg::Value(low), ir::BlockArg::Value(high)],
            done,
            &[],
        );

        self.builder.switch_to_block(swap);
        let low = self.builder.block_params(swap)[0];
        let high = self.builder.block_params(swap)[1];
        let front = self.list_cell(buffer, low);
        let back = self.list_cell(buffer, high);
        let first = self.builder.ins().load(machine, OWNED, front, 0);
        let second = self.builder.ins().load(machine, OWNED, back, 0);
        self.builder.ins().store(OWNED, second, front, 0);
        self.builder.ins().store(OWNED, first, back, 0);
        let low = self.builder.ins().iadd_imm(low, 1);
        let high = self.builder.ins().iadd_imm(high, -1);
        self.builder
            .ins()
            .jump(scan, &[ir::BlockArg::Value(low), ir::BlockArg::Value(high)]);

        self.builder.switch_to_block(done);
    }

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

    fn list_contains(&mut self, receiver: Value, value: Value, element: &Ty) -> Option<ir::Value> {
        let (index, length) = self.list_find(receiver, value, element)?;
        Some(
            self.builder
                .ins()
                .icmp(IntCC::UnsignedLessThan, index, length),
        )
    }

    /// The index of the first element equal to `value`, and the length,
    /// which the index equals where there is none.
    fn list_find(
        &mut self,
        receiver: Value,
        value: Value,
        element: &Ty,
    ) -> Option<(ir::Value, ir::Value)> {
        let text = self.compared_by_text(element)?;
        let Some(machine) = machine(element, self.pointer) else {
            self.gap(format!("a list holding `{element}`"));
            return None;
        };
        let list = self.value(receiver);
        let wanted = self.value(value);
        let length = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::LENGTH);
        let buffer = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BUFFER);
        let scan = self.builder.create_block();
        let compare = self.builder.create_block();
        let done = self.builder.create_block();
        self.builder.append_block_param(scan, self.pointer);
        self.builder.append_block_param(compare, self.pointer);
        self.builder.append_block_param(done, self.pointer);
        let zero = self.builder.ins().iconst(self.pointer, 0);
        self.builder.ins().jump(scan, &[ir::BlockArg::Value(zero)]);

        self.builder.switch_to_block(scan);
        let index = self.builder.block_params(scan)[0];
        let more = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, index, length);
        self.builder.ins().brif(
            more,
            compare,
            &[ir::BlockArg::Value(index)],
            done,
            &[ir::BlockArg::Value(index)],
        );

        self.builder.switch_to_block(compare);
        let index = self.builder.block_params(compare)[0];
        let offset = self.builder.ins().imul_imm(index, i64::from(layout::CELL));
        let cell = self.builder.ins().iadd(buffer, offset);
        let held = self.builder.ins().load(machine, OWNED, cell, 0);
        let same = if text {
            let call = self.builder.ins().call(self.text_equal, &[held, wanted]);
            self.builder.inst_results(call)[0]
        } else {
            self.builder.ins().icmp(IntCC::Equal, held, wanted)
        };
        let following = self.builder.ins().iadd_imm(index, 1);
        self.builder.ins().brif(
            same,
            done,
            &[ir::BlockArg::Value(index)],
            scan,
            &[ir::BlockArg::Value(following)],
        );

        self.builder.switch_to_block(done);
        Some((self.builder.block_params(done)[0], length))
    }

    pub(super) fn contains(&mut self, receiver: Value, value: Value) -> Option<ir::Value> {
        let held = self.function.type_of(receiver).clone();
        if let Ty::Builtin {
            kind: Builtin::List | Builtin::FrozenList,
            args,
        } = &held
        {
            let Some(element) = args.first() else {
                self.gap("a list without an element type");
                return None;
            };
            return self.list_contains(receiver, value, element);
        }
        let bucket = self.find_bucket(receiver, value)?;
        Some(self.builder.ins().icmp_imm(IntCC::NotEqual, bucket, 0))
    }

    pub(super) fn index_of(
        &mut self,
        receiver: Value,
        value: Value,
        result: Option<Value>,
    ) -> Option<ir::Value> {
        let optional = self.function.type_of(result?).clone();
        let held = self.function.type_of(receiver).clone();
        let Ty::Builtin {
            kind: Builtin::List | Builtin::FrozenList,
            args,
        } = &held
        else {
            self.gap(format!("an index lookup in `{held}`"));
            return None;
        };
        let Some(element) = args.first() else {
            self.gap("a list without an element type");
            return None;
        };
        let (index, length) = self.list_find(receiver, value, element)?;
        let present = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, index, length);
        let built = self.allocate(&optional, 0)?;
        let tag = self.builder.ins().uextend(TAG_TYPE, present);
        self.builder.ins().store(OWNED, tag, built, TAG);
        self.builder.ins().store(OWNED, index, built, layout::CELL);
        Some(built)
    }

    pub(super) fn set_index(&mut self, receiver: Value, index: Value, value: Value) {
        let held = self.function.type_of(receiver).clone();
        match &held {
            Ty::Builtin {
                kind: Builtin::List,
                ..
            } => {
                let address = self.element_address(receiver, index);
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
            _ => self.gap(format!("indexing a value of type `{held}`")),
        }
    }

    /// LR70: the cell of element `index`, after trapping where the list has
    /// no such element.
    fn element_address(&mut self, receiver: Value, index: Value) -> ir::Value {
        let list = self.value(receiver);
        let index = self.value(index);
        let length = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::LENGTH);
        let outside = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedGreaterThanOrEqual, index, length);
        self.trap_if(outside, Trap::Bounds);
        let buffer = self
            .builder
            .ins()
            .load(self.pointer, OWNED, list, layout::BUFFER);
        let offset = self.builder.ins().imul_imm(index, i64::from(layout::CELL));
        self.builder.ins().iadd(buffer, offset)
    }
}
