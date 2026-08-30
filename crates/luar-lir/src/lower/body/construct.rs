//! Lowering constructors, fields, and collection literals.

use luar_ast::{Argument, Expr, ExprKind, FieldInit, MapEntry, MapKey};
use luar_diagnostics::Span;

use crate::inst::{Const, InstKind, Target, Terminator, Value};
use crate::lower::Property;
use crate::lower::body::Body;
use crate::program::FuncId;
use crate::ty::{Builtin, Ty};

impl<'a> Body<'a> {
    /// LR12.1, LR12.2: a literal gives a value for every field, and a field
    /// with a default may be left out.
    pub(super) fn record(
        &mut self,
        path: &[String],
        fields: &[FieldInit],
        wanted: Option<&Ty>,
        span: Span,
    ) -> Value {
        let ty = match self.recorded(span) {
            Ty::Never => match wanted {
                Some(wanted) => wanted.clone(),
                None => return self.missing(span, "a record literal with no type"),
            },
            recorded => recorded,
        };

        // LR15.3: a variant carrying named fields is written like a record
        // literal, and builds an enum value.
        if let Some(name) = path.last()
            && let Some(tag) = self.variant_of(&ty, name)
        {
            return self.construct_record(ty, tag, fields, span);
        }

        let Some(declared) = self.fields_of(&ty) else {
            return self.missing(span, "a record literal of a type with no fields");
        };

        let mut filled: Vec<Option<Value>> = vec![None; declared.len()];
        for init in fields {
            let slot = declared.iter().position(|(name, _)| *name == init.name);
            let value = self.stored(&init.value, slot.map(|slot| &declared[slot].1));
            if let Some(slot) = slot {
                filled[slot] = Some(value);
            }
        }

        for (slot, (_, held)) in declared.iter().enumerate() {
            if filled[slot].is_some() {
                continue;
            }

            let index = u32::try_from(slot).expect("field count fits in u32");
            let default = match &ty {
                Ty::Named { id, .. } => self.context.defaults.get(&(*id, index)).cloned(),
                _ => None,
            };

            filled[slot] = Some(match default {
                Some(default) => self.stored(&default, Some(held)),
                // LR12.1: a field a record leaves out is one nothing was given
                // for, which only an optional field may be.
                None if held.is_optional() => {
                    self.emit(InstKind::Const(Const::Nil), held.clone(), span)
                }
                None => return self.missing(span, "a literal with no value for a field"),
            });
        }

        let values = filled.into_iter().flatten().collect();
        self.emit(
            InstKind::MakeStruct {
                ty: ty.clone(),
                fields: values,
            },
            ty,
            span,
        )
    }

    /// LR12.2: `.` reads a field. LR8: `?.` reads one through a value that
    /// may hold nothing, and gives nothing back where it does.
    pub(super) fn field(
        &mut self,
        receiver: &Expr,
        name: &str,
        optional: bool,
        span: Span,
    ) -> Value {
        // LR15.3: a variant with no payload is written like a field of the
        // enum, and builds a value rather than reading one.
        if let ExprKind::Name(written) = &receiver.kind
            && self.lookup(written).is_none()
        {
            let ty = self.recorded(span);
            if let Some(variant) = self.variant_of(&ty, name) {
                return self.emit(
                    InstKind::MakeEnum {
                        ty: ty.clone(),
                        variant,
                        payload: Vec::new(),
                    },
                    ty,
                    span,
                );
            }
        }

        let object = self.expr(receiver, None);
        let result = self.recorded(span);

        if !optional {
            let object = self.settled(object, span);
            let held = self.function.type_of(object).clone();

            // LR43: a property reads like a field and runs code, so a read of
            // one is a call to its getter.
            if let Some((get, ty)) = self.getter(&held, name) {
                return self.emit(
                    InstKind::Call {
                        callee: get,
                        type_args: Vec::new(),
                        args: vec![object],
                    },
                    ty,
                    span,
                );
            }

            // LR13: `length` is read off the collection's header.
            if name == "length"
                && matches!(
                    held,
                    Ty::Builtin {
                        kind: Builtin::List
                            | Builtin::FrozenList
                            | Builtin::Map
                            | Builtin::FrozenMap
                            | Builtin::Set
                            | Builtin::FrozenSet,
                        ..
                    }
                )
            {
                return self.emit(InstKind::Length { receiver: object }, Ty::INT, span);
            }

            // LR37: strings store their byte length in the same header slot.
            if name == "byteLength" && matches!(held, Ty::Str) {
                return self.emit(InstKind::Length { receiver: object }, Ty::INT, span);
            }

            let Some(index) = self.field_index(&held, name) else {
                return self.missing(span, "a member that is not a stored field");
            };

            // LR57: a field the checker proved holds something reads as what
            // it holds.
            let declared = self
                .fields_of(&held)
                .and_then(|fields| fields.get(index as usize).map(|(_, ty)| ty.clone()));
            let read = InstKind::GetField {
                object,
                field: index,
            };
            if let Some(narrowed) = self.narrowed_from(declared, &result, read, span) {
                return narrowed;
            }

            return self.emit(
                InstKind::GetField {
                    object,
                    field: index,
                },
                result,
                span,
            );
        }

        let Ty::Optional(inner) = self.function.type_of(object).clone() else {
            return self.missing(span, "`?.` on a value that holds something already");
        };
        let Some(index) = self.field_index(&inner, name) else {
            return self.missing(span, "a member that is not a stored field");
        };
        let read = result.clone().without_optional();

        let present = self.function.add_block();
        let absent = self.function.add_block();
        let join = self.function.add_block();
        let there = self.emit(InstKind::IsSome { value: object }, Ty::Bool, span);
        self.terminate(Terminator::Branch {
            condition: there,
            then: Target::to(present),
            otherwise: Target::to(absent),
        });

        self.switch_to(present);
        let inside = self.emit(InstKind::Unwrap { value: object }, (*inner).clone(), span);
        let read = self.emit(
            InstKind::GetField {
                object: inside,
                field: index,
            },
            read,
            span,
        );
        let wrapped = self.coerce(read, &result, span);
        self.terminate(Terminator::Jump(Target::new(join, vec![wrapped])));

        self.switch_to(absent);
        let nothing = self.emit(InstKind::Const(Const::Nil), result.clone(), span);
        self.terminate(Terminator::Jump(Target::new(join, vec![nothing])));

        self.switch_to(join);
        self.function.add_block_param(join, result)
    }

    /// LR15.3: building an enum value from the payload the variant carries.
    pub(super) fn construct(
        &mut self,
        ty: Ty,
        variant: u32,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let Some(carried) = self.payload_of(&ty, variant) else {
            return self.missing(span, "a variant whose payload has no type");
        };
        if carried.len() != args.len() {
            return self.missing(span, "a variant given a payload of another length");
        }

        let payload = args
            .iter()
            .zip(&carried)
            .map(|(argument, held)| self.stored(&argument.value, Some(held)))
            .collect();

        self.emit(
            InstKind::MakeEnum {
                ty: ty.clone(),
                variant,
                payload,
            },
            ty,
            span,
        )
    }

    /// LR13.1, LR71: `[a, b]` fills a list or a fixed-size array, and which
    /// one it fills is what context asked for.
    pub(super) fn list(&mut self, values: &[Expr], wanted: Option<&Ty>, span: Span) -> Value {
        let ty = self.settled_type(wanted, span);
        let element = match &ty {
            Ty::Builtin { args, .. } => args.first().cloned(),
            Ty::Array(element, _) => Some((**element).clone()),
            _ => None,
        };
        let Some(element) = element else {
            return self.missing(span, "a sequence literal whose elements have no type");
        };

        let values = values
            .iter()
            .map(|value| self.expr(value, Some(&element)))
            .collect();
        self.emit(InstKind::MakeList { element, values }, ty, span)
    }

    /// LR13.2: `Map { ... }` builds a map, by name or by computed key.
    pub(super) fn map(&mut self, entries: &[MapEntry], wanted: Option<&Ty>, span: Span) -> Value {
        let ty = self.settled_type(wanted, span);
        let Ty::Builtin { args, .. } = &ty else {
            return self.missing(span, "a map literal whose entries have no type");
        };
        let (Some(key), Some(value)) = (args.first().cloned(), args.get(1).cloned()) else {
            return self.missing(span, "a map literal whose entries have no type");
        };

        let mut built = Vec::with_capacity(entries.len());
        for entry in entries {
            // LR55: an entry's key is written before its value, so it is
            // evaluated first.
            let held = match &entry.key {
                MapKey::Name(name) => {
                    self.emit(InstKind::Const(Const::Str(name.clone())), key.clone(), span)
                }
                MapKey::Computed(computed) => self.expr(computed, Some(&key)),
            };
            built.push((held, self.expr(&entry.value, Some(&value))));
        }

        self.emit(
            InstKind::MakeMap {
                key,
                value,
                entries: built,
            },
            ty,
            span,
        )
    }

    /// LR13.3: `Set { ... }` builds a set.
    pub(super) fn set(&mut self, values: &[Expr], wanted: Option<&Ty>, span: Span) -> Value {
        let ty = self.settled_type(wanted, span);
        let Ty::Builtin { args, .. } = &ty else {
            return self.missing(span, "a set literal whose elements have no type");
        };
        let Some(element) = args.first().cloned() else {
            return self.missing(span, "a set literal whose elements have no type");
        };
        let values = values
            .iter()
            .map(|value| self.expr(value, Some(&element)))
            .collect();
        self.emit(InstKind::MakeSet { element, values }, ty, span)
    }

    /// LR37: `x[i]` reads what the container holds at `i`. LR69: a map hands
    /// back an optional, because a key it does not hold is not a mistake.
    pub(super) fn index(
        &mut self,
        receiver: &Expr,
        index: &Expr,
        optional: bool,
        span: Span,
    ) -> Value {
        if optional {
            return self.missing(span, "an optional index");
        }

        // LR55: the container is written before the index, so it is evaluated
        // first.
        // LR36: a type the checker sent through `Index` reads through the
        // method it named.
        if self.context.facts.call(span).is_some() {
            let args = vec![Argument {
                name: None,
                value: index.clone(),
                span: index.span,
            }];
            return self.call(receiver, Some("index"), &args, span);
        }

        let container = self.expr(receiver, None);
        let container = self.settled(container, span);
        let held = self.function.type_of(container).clone();
        let key = match &held {
            Ty::Builtin { args, .. } => args.first().cloned(),
            Ty::Array(..) | Ty::Bytes => Some(Ty::INT),
            _ => return self.missing(span, "indexing something the compiler cannot index"),
        };

        // LR37, LR71: a list and an array are keyed by position, and only a
        // map states what it is keyed by.
        let wanted = match &held {
            Ty::Builtin {
                kind: Builtin::Map | Builtin::FrozenMap,
                ..
            } => key,
            _ => Some(Ty::INT),
        };

        let index = self.expr(index, wanted.as_ref());
        let result = self.recorded(span);

        if matches!(
            result,
            Ty::Builtin {
                kind: Builtin::Slice,
                ..
            }
        ) {
            let inclusive = matches!(
                self.function.type_of(index),
                Ty::Builtin {
                    kind: Builtin::RangeInclusive,
                    ..
                }
            );
            return self.emit(
                InstKind::MakeSlice {
                    receiver: container,
                    range: index,
                    inclusive,
                },
                result,
                span,
            );
        }

        // LR69: a map gives back `V?`. LR57: an element the checker proved
        // holds something reads as what it holds.
        if let Ty::Builtin {
            kind: Builtin::Map | Builtin::FrozenMap,
            args,
        } = &held
            && let Some(value) = args.get(1)
            && *value == result
        {
            let stored = self.emit(
                InstKind::GetIndex {
                    receiver: container,
                    index,
                },
                Ty::Optional(Box::new(value.clone())),
                span,
            );
            return self.emit(InstKind::Unwrap { value: stored }, result, span);
        }

        let element = match &held {
            Ty::Builtin {
                kind: Builtin::List | Builtin::FrozenList | Builtin::Slice,
                args,
            } => args.first().cloned(),
            Ty::Array(element, _) => Some(element.as_ref().clone()),
            Ty::Bytes => Some(Ty::Int(crate::ty::IntTy::U8)),
            _ => None,
        };
        let read = InstKind::GetIndex {
            receiver: container,
            index,
        };
        if let Some(narrowed) = self.narrowed_from(element, &result, read, span) {
            return narrowed;
        }

        self.emit(
            InstKind::GetIndex {
                receiver: container,
                index,
            },
            result,
            span,
        )
    }

    /// LR15.3: building an enum value whose variant carries named fields.
    fn construct_record(
        &mut self,
        ty: Ty,
        variant: u32,
        fields: &[FieldInit],
        span: Span,
    ) -> Value {
        let (Some(names), Some(carried)) = (
            self.payload_names(&ty, variant),
            self.payload_of(&ty, variant),
        ) else {
            return self.missing(span, "a variant whose payload has no type");
        };

        let mut filled: Vec<Option<Value>> = vec![None; names.len()];
        for init in fields {
            let slot = names.iter().position(|name| *name == init.name);
            let value = self.expr(&init.value, slot.map(|slot| &carried[slot]));
            if let Some(slot) = slot {
                filled[slot] = Some(value);
            }
        }

        if filled.iter().any(Option::is_none) {
            return self.missing(span, "a variant with no value for a field it carries");
        }

        let payload = filled.into_iter().flatten().collect();
        self.emit(
            InstKind::MakeEnum {
                ty: ty.clone(),
                variant,
                payload,
            },
            ty,
            span,
        )
    }

    /// The property `name` names on `ty`, if it names one (LR43).
    pub(super) fn property(&self, ty: &Ty, name: &str) -> Option<&Property> {
        let Ty::Named { id, .. } = ty else {
            return None;
        };
        self.context.properties.get(&(*id, name.to_owned()))
    }

    /// The function a read of `name` goes through, and what it gives back.
    pub(super) fn getter(&self, ty: &Ty, name: &str) -> Option<(FuncId, Ty)> {
        let Ty::Named { args, .. } = ty else {
            return None;
        };
        let held = self.property(ty, name)?;
        // LR19: a property of `Box<int>` gives back what `T` is filled with.
        let params = self.owner_params(ty)?;
        Some((held.get, held.ty.substitute(&params, args)))
    }

    fn owner_params(&self, ty: &Ty) -> Option<Vec<String>> {
        let Ty::Named { id, .. } = ty else {
            return None;
        };
        Some(self.context.program.nominal(*id).type_params.clone())
    }

    pub(super) fn field_index(&self, ty: &Ty, name: &str) -> Option<u32> {
        let index = self
            .fields_of(ty)?
            .iter()
            .position(|(held, _)| held == name)?;
        u32::try_from(index).ok()
    }
}
