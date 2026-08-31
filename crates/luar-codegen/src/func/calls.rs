//! Calls: direct, through a closure, through an interface value, and the
//! assertion that aborts.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{self, AbiParam, InstBuilder, Signature, types};
use luar_lir::inst::{MethodId, Value};
use luar_lir::program::{FuncId, Shape};
use luar_lir::ty::{Ty, TypeId};

use crate::abi::{CAbi, Param as CParam, Result as CResult};
use crate::layout;
use crate::ty::machine;

use super::{AFTER_HANDLER, ASSERTION_FAILURE, OWNED, Translator};

impl Translator<'_, '_> {
    pub(super) fn call(
        &mut self,
        callee: FuncId,
        type_args: &[Ty],
        args: &[Value],
    ) -> Option<ir::Value> {
        if !type_args.is_empty() {
            self.gap("a call monomorphization left generic");
            return None;
        }
        let Some(reference) = self.callees.get(&callee).copied() else {
            self.gap("a call to a function the backend did not emit");
            return None;
        };
        if let Some(abi) = self.external_abis.get(&callee).cloned() {
            return self.call_external(callee, args, reference, &abi);
        }
        let passed: Vec<ir::Value> = args.iter().map(|arg| self.value(*arg)).collect();
        let call = self.builder.ins().call(reference, &passed);
        match self.builder.inst_results(call).first().copied() {
            Some(result) => Some(result),
            None if self.program.function(callee).result == Ty::Unit => {
                Some(self.builder.ins().iconst(types::I8, 0))
            }
            None => {
                self.gap("a call whose result the ABI did not return");
                None
            }
        }
    }

    fn call_external(
        &mut self,
        callee: FuncId,
        args: &[Value],
        reference: ir::FuncRef,
        abi: &CAbi,
    ) -> Option<ir::Value> {
        let result_ty = self.program.function(callee).result.clone();
        let returned = if matches!(abi.result, CResult::Indirect) {
            Some(self.allocate(&result_ty, 0)?)
        } else {
            None
        };

        let mut passed = Vec::new();
        if let Some(returned) = returned {
            passed.push(returned);
        }
        for (value, param) in args.iter().zip(&abi.params) {
            let value = self.value(*value);
            match param {
                CParam::Scalar | CParam::Indirect | CParam::Stack(_) => passed.push(value),
                CParam::Direct(parts) => {
                    for part in parts {
                        passed.push(self.builder.ins().load(part.ty, OWNED, value, part.offset));
                    }
                }
            }
        }

        let call = self.builder.ins().call(reference, &passed);
        match &abi.result {
            CResult::Unit => Some(self.builder.ins().iconst(types::I8, 0)),
            CResult::Scalar => self.builder.inst_results(call).first().copied(),
            CResult::Indirect => returned,
            CResult::Direct(parts) => {
                let result = self.allocate(&result_ty, 0)?;
                let values = self.builder.inst_results(call).to_vec();
                for (part, value) in parts.iter().zip(values) {
                    self.builder.ins().store(OWNED, value, result, part.offset);
                }
                Some(result)
            }
        }
    }

    pub(super) fn make_dyn(
        &mut self,
        interface: Option<TypeId>,
        value: Value,
        result: Option<Value>,
    ) -> Option<ir::Value> {
        let held = self.function.type_of(value).clone();
        let first = match interface {
            None => self.descriptors.get(&held).copied(),
            Some(interface) => self.vtables.get(&(interface, held.clone())).copied(),
        };
        let Some(first) = first else {
            self.gap(format!("a dynamic value holding `{held}`"));
            return None;
        };
        // A method reached through the table takes the value as a word, so
        // the value has to be one.
        if interface.is_some()
            && machine(&held, self.pointer).is_none_or(|ty| ty.bytes() != self.pointer.bytes())
        {
            self.gap(format!("an interface value holding `{held}`"));
            return None;
        }
        let ty = self.function.type_of(result?).clone();
        let built = self.allocate_bytes(layout::CELL * 2, &ty, 0)?;
        let first = self.builder.ins().global_value(self.pointer, first);
        self.builder.ins().store(OWNED, first, built, 0);
        self.write_at(built, &ty, 1, value);
        Some(built)
    }

    /// A call through an interface value: the method's slot in the table the
    /// value carries, given what the value holds (LR18.1).
    pub(super) fn call_virtual(
        &mut self,
        method: MethodId,
        receiver: Value,
        args: &[Value],
    ) -> Option<ir::Value> {
        let Shape::Interface(interface) = &self.program.nominal(method.interface).shape else {
            self.gap("a call through something that is not an interface");
            return None;
        };
        let Some(declared) = interface.methods.get(method.slot as usize) else {
            self.gap("a call to a method slot the interface does not have");
            return None;
        };
        let (params, result) = (declared.params.clone(), declared.result.clone());
        let signature = self.indirect_signature(&params, &result)?;

        let object = self.value(receiver);
        let table = self.builder.ins().load(self.pointer, OWNED, object, 0);
        let offset = i32::try_from(method.slot).unwrap_or(i32::MAX) * self.pointer.bytes() as i32;
        let code = self.builder.ins().load(self.pointer, OWNED, table, offset);
        let inner = self
            .builder
            .ins()
            .load(self.pointer, OWNED, object, layout::CELL);
        let mut passed = vec![inner];
        passed.extend(args.iter().map(|arg| self.value(*arg)));
        let call = self.builder.ins().call_indirect(signature, code, &passed);
        self.builder.inst_results(call).first().copied()
    }

    /// The signature of code called through a value: a word first, then the
    /// parameters, and the result.
    fn indirect_signature(&mut self, params: &[Ty], result: &Ty) -> Option<ir::SigRef> {
        let mut signature = Signature::new(self.builder.func.signature.call_conv);
        signature.params.push(AbiParam::new(self.pointer));
        for param in params {
            let Some(held) = machine(param, self.pointer) else {
                self.gap(format!("a call through a value passing `{param}`"));
                return None;
            };
            signature.params.push(AbiParam::new(held));
        }
        let Some(returned) = machine(result, self.pointer) else {
            self.gap(format!("a call through a value returning `{result}`"));
            return None;
        };
        signature.returns.push(AbiParam::new(returned));
        Some(self.builder.import_signature(signature))
    }

    /// A call through a closure, whose code takes the closure first.
    pub(super) fn call_indirect(
        &mut self,
        callee: Value,
        args: &[Value],
        result: Option<Value>,
    ) -> Option<ir::Value> {
        let Ty::Function { params, .. } = self.function.type_of(callee).clone() else {
            self.gap("a call through something that is not a function");
            return None;
        };
        let result = self.function.type_of(result?).clone();
        let signature = self.indirect_signature(&params, &result)?;

        let closure = self.value(callee);
        let code = self.builder.ins().load(self.pointer, OWNED, closure, 0);
        let mut passed = vec![closure];
        passed.extend(args.iter().map(|arg| self.value(*arg)));
        let call = self.builder.ins().call_indirect(signature, code, &passed);
        self.builder.inst_results(call).first().copied()
    }

    pub(super) fn assert(&mut self, condition: Value, message: Option<Value>) {
        let condition = self.value(condition);
        let failed = self.builder.ins().icmp_imm(IntCC::Equal, condition, 0);
        let failing = self.builder.create_block();
        let carry_on = self.builder.create_block();
        self.builder.ins().brif(failed, failing, &[], carry_on, &[]);

        self.builder.switch_to_block(failing);
        let message = match message {
            Some(message) => self.value(message),
            None => self.builder.ins().iconst(self.pointer, 0),
        };
        let kind = self.builder.ins().iconst(types::I8, ASSERTION_FAILURE);
        self.builder.ins().call(self.abort, &[kind, message]);
        self.builder.ins().trap(AFTER_HANDLER);
        self.builder.switch_to_block(carry_on);
    }
}
