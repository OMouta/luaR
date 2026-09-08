//! Writing a function's blocks by hand.

use luar_diagnostics::Span;

use crate::inst::{BinaryOp, Const, Inst, InstKind, Target, Terminator, Trap, UnaryOp, Value};
use crate::program::{BlockId, FuncId, Function};
use crate::ty::Ty;

pub(super) struct Builder<'a> {
    pub function: &'a mut Function,
    pub current: BlockId,
    pub span: Span,
}

impl<'a> Builder<'a> {
    pub fn new(function: &'a mut Function, current: BlockId, span: Span) -> Self {
        Self {
            function,
            current,
            span,
        }
    }

    pub fn emit(&mut self, kind: InstKind, ty: Ty) -> Value {
        let result = self.function.add_value(ty);
        self.function.block_mut(self.current).insts.push(Inst {
            result: Some(result),
            kind,
            span: self.span,
        });
        result
    }

    pub fn emit_void(&mut self, kind: InstKind) {
        self.function.block_mut(self.current).insts.push(Inst {
            result: None,
            kind,
            span: self.span,
        });
    }

    pub fn terminate(&mut self, term: Terminator) {
        self.function.block_mut(self.current).term = Some(term);
    }

    pub fn block(&mut self) -> BlockId {
        self.function.add_block()
    }

    pub fn param(&mut self, block: BlockId, ty: Ty) -> Value {
        self.function.add_block_param(block, ty)
    }

    pub fn switch_to(&mut self, block: BlockId) {
        self.current = block;
    }

    pub fn jump(&mut self, block: BlockId) {
        self.terminate(Terminator::Jump(Target::to(block)));
    }

    pub fn jump_with(&mut self, block: BlockId, args: Vec<Value>) {
        self.terminate(Terminator::Jump(Target::new(block, args)));
    }

    pub fn branch(&mut self, condition: Value, then: BlockId, otherwise: BlockId) {
        self.terminate(Terminator::Branch {
            condition,
            then: Target::to(then),
            otherwise: Target::to(otherwise),
        });
    }

    pub fn ret(&mut self, value: Value) {
        self.terminate(Terminator::Return(value));
    }

    pub fn int(&mut self, value: i64) -> Value {
        self.emit(InstKind::Const(Const::Int(value as u64)), Ty::INT)
    }

    pub fn bool(&mut self, value: bool) -> Value {
        self.emit(InstKind::Const(Const::Bool(value)), Ty::Bool)
    }

    pub fn unit(&mut self) -> Value {
        self.emit(InstKind::Const(Const::Unit), Ty::Unit)
    }

    pub fn nil(&mut self, ty: Ty) -> Value {
        self.emit(InstKind::Const(Const::Nil), ty)
    }

    pub fn get(&mut self, object: Value, field: u32, ty: Ty) -> Value {
        self.emit(InstKind::GetField { object, field }, ty)
    }

    pub fn set(&mut self, object: Value, field: u32, value: Value) {
        self.emit_void(InstKind::SetField {
            object,
            field,
            value,
        });
    }

    pub fn is_some(&mut self, value: Value) -> Value {
        self.emit(InstKind::IsSome { value }, Ty::Bool)
    }

    pub fn unwrap(&mut self, value: Value, ty: Ty) -> Value {
        self.emit(InstKind::Unwrap { value }, ty)
    }

    pub fn some(&mut self, value: Value) -> Value {
        let ty = Ty::Optional(Box::new(self.function.type_of(value).clone()));
        self.emit(InstKind::MakeSome { value }, ty)
    }

    pub fn call(&mut self, callee: FuncId, args: Vec<Value>, ty: Ty) -> Value {
        self.emit(
            InstKind::Call {
                callee,
                type_args: Vec::new(),
                args,
            },
            ty,
        )
    }

    pub fn equal(&mut self, left: Value, right: Value) -> Value {
        self.emit(
            InstKind::Binary {
                op: BinaryOp::Equal,
                left,
                right,
            },
            Ty::Bool,
        )
    }

    pub fn add(&mut self, left: Value, right: Value) -> Value {
        self.emit(
            InstKind::Binary {
                op: BinaryOp::Add,
                left,
                right,
            },
            Ty::INT,
        )
    }

    pub fn not(&mut self, operand: Value) -> Value {
        self.emit(
            InstKind::Unary {
                op: UnaryOp::Not,
                operand,
            },
            Ty::Bool,
        )
    }

    pub fn and(&mut self, left: Value, right: Value) -> Value {
        self.emit(
            InstKind::Binary {
                op: BinaryOp::BitAnd,
                left,
                right,
            },
            Ty::Bool,
        )
    }

    pub fn length(&mut self, receiver: Value) -> Value {
        self.emit(InstKind::Length { receiver }, Ty::INT)
    }

    pub fn index(&mut self, receiver: Value, index: Value, ty: Ty) -> Value {
        self.emit(InstKind::GetIndex { receiver, index }, ty)
    }

    pub fn boxed(&mut self, value: Value) -> Value {
        self.emit(
            InstKind::MakeDyn {
                interface: None,
                value,
            },
            Ty::Dynamic,
        )
    }

    pub fn unboxed(&mut self, value: Value, ty: Ty) -> Value {
        self.emit(InstKind::DynValue { value }, ty)
    }

    pub fn panic(&mut self, message: &str) {
        let message = self.emit(InstKind::Const(Const::Str(message.to_owned())), Ty::Str);
        self.emit_void(InstKind::Panic { message });
        self.terminate(Terminator::Trap(Trap::Unreachable));
    }
}
