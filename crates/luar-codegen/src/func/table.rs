//! Maps and sets (LR13.2, LR13.3), emitted over the runtime's table.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{self, InstBuilder, types};
use luar_lir::inst::Value;
use luar_lir::ty::{Builtin, Ty};

use crate::layout::{self, TAG, TAG_TYPE};
use crate::ty::machine;

use super::{OWNED, Translator};

impl Translator<'_, '_> {
    /// LR13.2: a map starts empty and takes its entries one at a time, so
    /// the runtime decides its capacity.
    pub(super) fn make_map(
        &mut self,
        result: Option<Value>,
        entries: &[(Value, Value)],
    ) -> Option<ir::Value> {
        let ty = self.function.type_of(result?).clone();
        let Ty::Builtin { args, .. } = &ty else {
            return None;
        };
        let text = self.compared_by_text(args.first()?)?;
        let header = self.allocate(&ty, 0)?;
        let zero = self.builder.ins().iconst(self.pointer, 0);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::LENGTH);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::CAPACITY);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::BUFFER);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::BORROWS);
        for (key, value) in entries {
            let bucket = self.map_insert(header, *key, text)?;
            let written = self.value(*value);
            self.builder
                .ins()
                .store(OWNED, written, bucket, layout::BUCKET_VALUE);
        }
        Some(header)
    }

    /// LR13.3: a set stores each distinct value as a table key.
    pub(super) fn make_set(
        &mut self,
        result: Option<Value>,
        values: &[Value],
    ) -> Option<ir::Value> {
        let ty = self.function.type_of(result?).clone();
        let Ty::Builtin { args, .. } = &ty else {
            return None;
        };
        let text = self.compared_by_text(args.first()?)?;
        let header = self.allocate(&ty, 0)?;
        let zero = self.builder.ins().iconst(self.pointer, 0);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::LENGTH);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::CAPACITY);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::BUFFER);
        self.builder
            .ins()
            .store(OWNED, zero, header, layout::BORROWS);
        for value in values {
            self.map_insert(header, *value, text)?;
        }
        Some(header)
    }

    pub(super) fn set_insert(&mut self, receiver: Value, value: Value) {
        let held = self.function.type_of(receiver).clone();
        let Ty::Builtin {
            kind: Builtin::Set,
            args,
        } = &held
        else {
            self.gap(format!("inserting into `{held}`"));
            return;
        };
        let Some(text) = args
            .first()
            .and_then(|element| self.compared_by_text(element))
        else {
            return;
        };
        let set = self.value(receiver);
        let _ = self.map_insert(set, value, text);
    }

    pub(super) fn map_remove(
        &mut self,
        receiver: Value,
        key: Value,
        result: Option<Value>,
    ) -> Option<ir::Value> {
        let optional = self.function.type_of(result?).clone();
        let Ty::Optional(inner) = &optional else {
            self.gap("a removal that is not optional");
            return None;
        };
        let Some(machine) = machine(inner, self.pointer) else {
            self.gap(format!("a map holding `{inner}`"));
            return None;
        };
        let bucket = self.find_bucket(receiver, key)?;
        let table = self.value(receiver);
        let present = self.builder.ins().icmp_imm(IntCC::NotEqual, bucket, 0);
        let built = self.allocate(&optional, 0)?;
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
        self.builder.ins().call(self.map_remove, &[table, bucket]);
        self.builder.ins().jump(carry_on, &[]);
        self.builder.switch_to_block(carry_on);
        Some(built)
    }

    pub(super) fn set_remove(&mut self, receiver: Value, value: Value) -> Option<ir::Value> {
        let bucket = self.find_bucket(receiver, value)?;
        let table = self.value(receiver);
        let present = self.builder.ins().icmp_imm(IntCC::NotEqual, bucket, 0);
        let found = self.builder.create_block();
        let carry_on = self.builder.create_block();
        self.builder.ins().brif(present, found, &[], carry_on, &[]);
        self.builder.switch_to_block(found);
        self.builder.ins().call(self.map_remove, &[table, bucket]);
        self.builder.ins().jump(carry_on, &[]);
        self.builder.switch_to_block(carry_on);
        Some(present)
    }

    pub(super) fn clear(&mut self, receiver: Value) {
        let held = self.function.type_of(receiver).clone();
        let table = self.value(receiver);
        let zero = self.builder.ins().iconst(self.pointer, 0);
        self.builder.ins().store(OWNED, zero, table, layout::LENGTH);
        match &held {
            Ty::Builtin {
                kind: Builtin::List,
                ..
            } => self.check_unborrowed(table),
            // At zero capacity `find` misses and the next insert allocates.
            Ty::Builtin {
                kind: Builtin::Map | Builtin::Set,
                ..
            } => {
                self.builder
                    .ins()
                    .store(OWNED, zero, table, layout::CAPACITY);
                self.builder.ins().store(OWNED, zero, table, layout::BUFFER);
            }
            _ => self.gap(format!("clearing `{held}`")),
        }
    }

    /// The bucket `key` occupies in the map or set `receiver`, or null.
    pub(super) fn find_bucket(&mut self, receiver: Value, key: Value) -> Option<ir::Value> {
        let held = self.function.type_of(receiver).clone();
        let Ty::Builtin {
            kind: Builtin::Map | Builtin::FrozenMap | Builtin::Set | Builtin::FrozenSet,
            args,
        } = &held
        else {
            self.gap(format!("looking up `{held}`"));
            return None;
        };
        let text = args
            .first()
            .and_then(|element| self.compared_by_text(element))?;
        let table = self.value(receiver);
        let hash = self.key_hash(key)?;
        let word = self.key_word(key);
        let text = self.builder.ins().iconst(types::I8, i64::from(text));
        let call = self
            .builder
            .ins()
            .call(self.map_find, &[table, word, hash, text]);
        self.builder.inst_results(call).first().copied()
    }

    /// Bucket `index` of the map or set `receiver`, below its bucket count.
    pub(super) fn bucket_address(&mut self, receiver: Value, index: Value) -> ir::Value {
        let table = self.value(receiver);
        let index = self.value(index);
        let buckets = self
            .builder
            .ins()
            .load(self.pointer, OWNED, table, layout::BUFFER);
        let offset = self.builder.ins().imul_imm(index, layout::BUCKET_BYTES);
        self.builder.ins().iadd(buckets, offset)
    }

    /// The bucket `key` occupies in `map`, claimed where it had none.
    pub(super) fn map_insert(
        &mut self,
        map: ir::Value,
        key: Value,
        text: bool,
    ) -> Option<ir::Value> {
        let hash = self.key_hash(key)?;
        let word = self.key_word(key);
        let text = self.builder.ins().iconst(types::I8, i64::from(text));
        let call = self
            .builder
            .ins()
            .call(self.map_insert, &[map, word, hash, text]);
        self.builder.inst_results(call).first().copied()
    }

    pub(super) fn key_hash(&mut self, key: Value) -> Option<ir::Value> {
        let hash = self.hash_value(key)?;
        Some(self.word_of(hash))
    }

    /// A key as the one word a bucket stores it in.
    pub(super) fn key_word(&mut self, key: Value) -> ir::Value {
        let value = self.value(key);
        self.word_of(value)
    }

    pub(super) fn word_of(&mut self, value: ir::Value) -> ir::Value {
        let held = self.builder.func.dfg.value_type(value);
        match held.bits().cmp(&self.pointer.bits()) {
            std::cmp::Ordering::Less => self.builder.ins().uextend(self.pointer, value),
            std::cmp::Ordering::Equal => value,
            std::cmp::Ordering::Greater => self.builder.ins().ireduce(self.pointer, value),
        }
    }

    /// Whether two values of `ty` are the same when their text is rather than
    /// when their words are, or `None` for a type the runtime cannot compare.
    pub(super) fn compared_by_text(&mut self, ty: &Ty) -> Option<bool> {
        match ty {
            Ty::Str | Ty::Bytes => Some(true),
            Ty::Bool | Ty::Int(_) | Ty::Char => Some(false),
            _ => {
                self.gap(format!("comparing `{ty}`"));
                None
            }
        }
    }

    pub(super) fn hash_value(&mut self, value: Value) -> Option<ir::Value> {
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
}
