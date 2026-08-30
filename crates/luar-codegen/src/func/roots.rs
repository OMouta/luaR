//! The shadow-stack frame and the stack slots of one function.

use cranelift_codegen::ir::{self, InstBuilder, StackSlotData, StackSlotKind};
use luar_lir::inst::Value;
use luar_lir::program::SlotId;

use crate::gc::ROOT_FRAME_HEADER;
use crate::layout;
use crate::ty::machine;

use super::{OWNED, Translator};

impl Translator<'_, '_> {
    pub(super) fn create_slots(&mut self) {
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

    pub(super) fn prepare_roots(&mut self) {
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

    pub(super) fn enter_roots(&mut self) {
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

    pub(super) fn leave_roots(&mut self) {
        let frame = self.builder.ins().stack_addr(
            self.pointer,
            self.root_frame.expect("root frame exists"),
            0,
        );
        let previous = self.builder.ins().load(self.pointer, OWNED, frame, 0);
        let top = self.builder.ins().global_value(self.pointer, self.roots);
        self.builder.ins().store(OWNED, previous, top, 0);
    }

    pub(super) fn root(&mut self, value: Value, machine: ir::Value) {
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

    pub(super) fn unroot(&mut self, value: Value) {
        let Some(offset) = self.root_offsets.get(&value).copied() else {
            return;
        };
        let frame = self.builder.ins().stack_addr(
            self.pointer,
            self.root_frame.expect("root frame exists"),
            0,
        );
        let zero = self.builder.ins().iconst(self.pointer, 0);
        self.builder.ins().store(OWNED, zero, frame, offset);
    }

    pub(super) fn root_temporary(&mut self, index: u32, machine: ir::Value) {
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
}
