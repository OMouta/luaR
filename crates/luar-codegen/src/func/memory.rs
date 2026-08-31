//! Managed storage: allocating it, and reading and writing its cells.

use cranelift_codegen::ir::{self, InstBuilder, StackSlotData, StackSlotKind, types};
use luar_lir::inst::{Allocation, Value};
use luar_lir::ty::{Builtin, Ty};

use crate::layout::{self, TAG_TYPE};
use crate::ty::machine;

use super::{OWNED, Translator};

impl Translator<'_, '_> {
    /// Storage large enough for a value of `ty`.
    pub(super) fn allocate(&mut self, ty: &Ty, temporary: u32) -> Option<ir::Value> {
        let Some(size) = layout::size(self.program, ty, self.pointer) else {
            self.gap(format!("storage for a value of type `{ty}`"));
            return None;
        };
        self.allocate_bytes(size, ty, temporary)
    }

    pub(super) fn allocate_bytes(
        &mut self,
        size: i32,
        ty: &Ty,
        temporary: u32,
    ) -> Option<ir::Value> {
        let size = self.builder.ins().iconst(self.pointer, i64::from(size));
        let finalizer = match ty {
            Ty::Builtin {
                kind: Builtin::Slice,
                ..
            } => self
                .builder
                .ins()
                .func_addr(self.pointer, self.slice_finalizer),
            _ => match self.finalizers.get(ty).copied() {
                Some(function) => self.builder.ins().func_addr(self.pointer, function),
                None => self.builder.ins().iconst(self.pointer, 0),
            },
        };
        let call = self.builder.ins().call(self.allocate, &[size, finalizer]);
        let allocated = self.builder.inst_results(call).first().copied()?;
        self.root_temporary(temporary, allocated);
        Some(allocated)
    }

    pub(super) fn allocate_stack(&mut self, ty: &Ty) -> Option<ir::Value> {
        let size = u32::try_from(layout::size(self.program, ty, self.pointer)?).ok()?;
        let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            size,
            self.pointer.bytes().ilog2() as u8,
        ));
        Some(self.builder.ins().stack_addr(self.pointer, slot, 0))
    }

    fn allocate_as(
        &mut self,
        ty: &Ty,
        temporary: u32,
        allocation: Allocation,
    ) -> Option<ir::Value> {
        match allocation {
            Allocation::Managed => self.allocate(ty, temporary),
            Allocation::Stack | Allocation::Registers => self.allocate_stack(ty),
        }
    }

    /// Reads cell `index` of the aggregate `object` points at.
    pub(super) fn read(
        &mut self,
        object: Value,
        index: u32,
        result: Option<Value>,
    ) -> Option<ir::Value> {
        let held = self.function.type_of(object).clone();
        let offset = layout::field_offset(self.program, &held, index, self.pointer)?;
        let address = self.value(object);
        let ty = result.map_or(types::I8, |value| self.machine_or_gap(value));
        Some(self.builder.ins().load(ty, OWNED, address, offset))
    }

    pub(super) fn write(&mut self, object: Value, index: u32, value: Value) {
        let ty = self.function.type_of(object).clone();
        let address = self.value(object);
        self.write_at(address, &ty, index, value);
    }

    pub(super) fn write_at(&mut self, address: ir::Value, owner: &Ty, index: u32, value: Value) {
        let Some(offset) = layout::field_offset(self.program, owner, index, self.pointer) else {
            self.gap(format!("a field outside `{owner}`"));
            return;
        };
        let written = self.value(value);
        self.builder.ins().store(OWNED, written, address, offset);
    }

    /// Storage for an aggregate, with `parts` written into the cells after
    /// `from`.
    pub(super) fn make(
        &mut self,
        ty: &Ty,
        from: u32,
        parts: &[Value],
        allocation: Allocation,
    ) -> Option<ir::Value> {
        let built = self.allocate_as(ty, 0, allocation)?;
        for (index, part) in parts.iter().enumerate() {
            let cell = from + u32::try_from(index).unwrap_or(u32::MAX);
            self.write_at(built, ty, cell, *part);
        }
        Some(built)
    }

    /// LR31: fresh storage holding what `source` holds. A cell holding a
    /// value struct is copied too, because mutating one through a shared
    /// holder would be observable through the other. A cell holding a
    /// reference keeps referring to the same object.
    pub(super) fn duplicate(
        &mut self,
        source: ir::Value,
        ty: &Ty,
        depth: u32,
        allocation: Allocation,
    ) -> Option<ir::Value> {
        let Some(size) = layout::size(self.program, ty, self.pointer) else {
            self.gap(format!("a copy of a value of type `{ty}`"));
            return None;
        };
        if depth == 0 {
            self.gap(format!("a copy of a value nested as deeply as `{ty}`"));
            return None;
        }

        let parts = layout::parts(self.program, ty);
        let copy = self.allocate_as(ty, layout::DEPTH - depth, allocation)?;
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
                    self.duplicate(held, part, depth - 1, allocation)
                        .unwrap_or(held)
                } else {
                    held
                };
                self.builder.ins().store(OWNED, written, copy, offset);
            }
        } else if let Some(variants) = layout::tagged_parts(self.program, ty) {
            let tag = self
                .builder
                .ins()
                .load(TAG_TYPE, OWNED, source, layout::TAG);
            self.builder.ins().store(OWNED, tag, copy, layout::TAG);
            let done = self.builder.create_block();
            let mut next = None;

            for (variant, parts) in variants.iter().enumerate() {
                if let Some(block) = next.take() {
                    self.builder.switch_to_block(block);
                }
                let active = self.builder.create_block();
                let otherwise = self.builder.create_block();
                let matches = self.builder.ins().icmp_imm(
                    cranelift_codegen::ir::condcodes::IntCC::Equal,
                    tag,
                    i64::try_from(variant).unwrap_or(i64::MAX),
                );
                self.builder
                    .ins()
                    .brif(matches, active, &[], otherwise, &[]);

                self.builder.switch_to_block(active);
                for (index, part) in parts.iter().enumerate() {
                    let field = u32::try_from(index + 1).expect("field count fits in u32");
                    let Some(offset) = layout::field_offset(self.program, ty, field, self.pointer)
                    else {
                        self.gap(format!("a field outside `{ty}`"));
                        continue;
                    };
                    let Some(machine) = machine(part, self.pointer) else {
                        self.gap(format!("a copy of a field of type `{part}`"));
                        continue;
                    };
                    let held = self.builder.ins().load(machine, OWNED, source, offset);
                    let written = if layout::holds_value_parts(self.program, part, layout::DEPTH) {
                        self.duplicate(held, part, depth - 1, allocation)
                            .unwrap_or(held)
                    } else {
                        held
                    };
                    self.builder.ins().store(OWNED, written, copy, offset);
                }
                self.builder.ins().jump(done, &[]);
                next = Some(otherwise);
            }

            if let Some(block) = next {
                self.builder.switch_to_block(block);
                self.builder.ins().jump(done, &[]);
            }
            self.builder.switch_to_block(done);
        } else {
            for cell in (0..size).step_by(layout::CELL as usize) {
                let held = self.builder.ins().load(TAG_TYPE, OWNED, source, cell);
                self.builder.ins().store(OWNED, held, copy, cell);
            }
        }
        Some(copy)
    }

    pub(super) fn reinterpret(&mut self, value: Value, to: &Ty) -> Option<ir::Value> {
        let from = self.function.type_of(value).clone();
        let source = self.value(value);
        let source_aggregate = layout::is_aggregate(&from);
        let target_aggregate = layout::is_aggregate(to);

        match (source_aggregate, target_aggregate) {
            (false, false) => {
                let source_ty = machine(&from, self.pointer)?;
                let target_ty = machine(to, self.pointer)?;
                if source_ty != target_ty {
                    self.gap(format!("reinterpretation from `{from}` to `{to}`"));
                    return None;
                }
                Some(source)
            }
            (false, true) => {
                let built = self.allocate(to, 0)?;
                self.builder.ins().store(OWNED, source, built, 0);
                Some(built)
            }
            (true, false) => {
                let target = machine(to, self.pointer)?;
                Some(self.builder.ins().load(target, OWNED, source, 0))
            }
            (true, true) => {
                let size = layout::abi_size(self.program, &from, self.pointer)?;
                let built = self.allocate(to, 0)?;
                let mut offset = 0;
                for (width, ty) in [
                    (8, types::I64),
                    (4, types::I32),
                    (2, types::I16),
                    (1, types::I8),
                ] {
                    while size - offset >= width {
                        let held = self.builder.ins().load(ty, OWNED, source, offset);
                        self.builder.ins().store(OWNED, held, built, offset);
                        offset += width;
                    }
                }
                Some(built)
            }
        }
    }
}
