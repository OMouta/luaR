//! Instructions, and what ends a block.

use luar_diagnostics::Span;

use crate::program::{BlockId, FuncId, SlotId};
use crate::ty::{Ty, TypeId};

/// A value, produced once and never again.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Value(pub u32);

/// One instruction, and the source it came from.
#[derive(Debug, Clone, PartialEq)]
pub struct Inst {
    /// The value it produces, absent where it produces none.
    pub result: Option<Value>,
    pub kind: InstKind,
    pub span: Span,
}

/// A literal, once context has said what type it has (LR4, LR39).
#[derive(Debug, Clone, PartialEq)]
pub enum Const {
    /// The one value of [`Ty::Unit`], which a function with no result gives
    /// back (LR9.1).
    Unit,
    /// `nil`, or an absent optional (LR4.1, LR8).
    Nil,
    Bool(bool),
    /// An integer, in the bits of its type. A negative `i8` is stored as the
    /// `u64` those eight bits spell, so the width is read from the value's
    /// type rather than from here.
    Int(u64),
    Float(f64),
    Char(char),
    Str(String),
    Bytes(Vec<u8>),
}

/// `-x`, `~x`, `not x` (LR11.1, LR11.4, LR11.5).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Negate,
    Not,
    BitNot,
}

/// A binary operator, once the checker has settled what its operands are.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    // LR11.1
    Add,
    Subtract,
    Multiply,
    Divide,
    IntegerDivide,
    Remainder,
    Power,
    /// `..` (LR11.2).
    Concat,
    // LR11.3
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    // LR11.5
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
}

/// What an overflow-explicit operation does where the ordinary operator
/// would trap (LR4.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Overflow {
    Wrap,
    Saturate,
    Check,
}

impl BinaryOp {
    /// Whether the operator can fail on values the type system allows:
    /// overflow on an integer (LR4.3), and a zero divisor (LR11.1).
    #[must_use]
    pub fn can_trap(self) -> bool {
        matches!(
            self,
            Self::Add
                | Self::Subtract
                | Self::Multiply
                | Self::Divide
                | Self::IntegerDivide
                | Self::Remainder
                | Self::Power
        )
    }
}

/// One method of an interface, by the slot it occupies in the interface's
/// method table (LR18.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MethodId {
    pub interface: TypeId,
    pub slot: u32,
}

/// What ends a program where it stands (LR4.3, LR11.1, LR50, LR70).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trap {
    /// An integer operation left the range of its type (LR4.3).
    IntegerOverflow,
    /// `//` or `%` by zero (LR11.1).
    DivisionByZero,
    /// An index outside what the container holds (LR70).
    Bounds,
    /// `unreachable()` was reached (LR50).
    Unreachable,
    /// A list changed while a slice borrowed its storage (LR38).
    BorrowedMutation,
}

impl Trap {
    #[must_use]
    pub fn spelling(self) -> &'static str {
        match self {
            Self::IntegerOverflow => "integer-overflow",
            Self::DivisionByZero => "division-by-zero",
            Self::Bounds => "bounds",
            Self::Unreachable => "unreachable",
            Self::BorrowedMutation => "borrowed-mutation",
        }
    }
}

/// What an instruction does besides producing its result, which is what
/// decides how far a pass may move it (LR55).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Effect {
    /// Nothing. The result depends only on the operands, so the instruction
    /// may be moved, repeated, or dropped where its result is unused.
    None,
    /// It may trap, and a trap stops the program at a point the source
    /// decides. It may move among instructions nothing can observe between,
    /// and never past one that can.
    Trap,
    /// It reads or writes state, or calls something that may. Its order
    /// against every other such instruction is what the program observes.
    State,
}

#[derive(Debug, Clone, PartialEq)]
pub enum InstKind {
    /// A literal (LR4).
    Const(Const),

    Unary {
        op: UnaryOp,
        operand: Value,
    },
    Binary {
        op: BinaryOp,
        left: Value,
        right: Value,
    },
    /// The `Hash` result for a primitive value (LR35, LR75).
    HashValue {
        value: Value,
    },
    /// Adds one field to a derived hash (LR75).
    HashCombine {
        state: Value,
        value: Value,
    },
    /// The `Display` result for a primitive value (LR35, LR75).
    DisplayValue {
        value: Value,
    },
    /// Writes a string followed by a newline (LR54.1).
    Print {
        value: Value,
    },
    /// The common error value holding `message` (LR54.1).
    MakeError {
        message: Value,
    },
    /// `assert` or an included `debugAssert` (LR49).
    Assert {
        condition: Value,
        message: Option<Value>,
    },
    /// `panic(message)` (LR25.4).
    Panic {
        message: Value,
    },

    /// `x as T`, between numeric types (LR33, LR39).
    Convert {
        value: Value,
        to: Ty,
    },
    /// A same-sized ABI representation copied without conversion (LR72).
    Reinterpret {
        value: Value,
        to: Ty,
    },
    /// `x is T` (LR57).
    IsType {
        value: Value,
        ty: Ty,
    },

    /// A call to a function named at compile time (LR9.1).
    Call {
        callee: FuncId,
        type_args: Vec<Ty>,
        args: Vec<Value>,
    },
    /// A call through a function value or a closure (LR9.2, LR9.8).
    CallIndirect {
        callee: Value,
        args: Vec<Value>,
    },
    /// A call through an interface value, dispatched at runtime until
    /// devirtualization proves one implementation (LR18.1).
    CallVirtual {
        method: MethodId,
        receiver: Value,
        args: Vec<Value>,
    },

    /// A value that carries what it is at runtime: one used through an
    /// interface, carrying which implementation to dispatch to (LR18.1), or
    /// an `any`, an `unknown`, or a thrown value, which name no interface
    /// (LR6.3, LR6.4, LR25.3).
    MakeDyn {
        interface: Option<TypeId>,
        value: Value,
    },
    /// The value inside one, where a check or a pass has proved what it holds
    /// (LR18.1, LR25.3).
    DynValue {
        value: Value,
    },

    /// A closure, over the values it captured (LR9.8).
    MakeClosure {
        func: FuncId,
        captures: Vec<Value>,
    },

    /// A fresh copy of an aggregate, one level deep, which is what a value
    /// struct is given when it reaches a new holder (LR31).
    CopyValue {
        value: Value,
    },
    /// A mutable collection viewed through its frozen type (LR59).
    Freeze {
        value: Value,
    },

    /// A struct or record value, its fields in declaration order (LR12).
    MakeStruct {
        ty: Ty,
        fields: Vec<Value>,
    },
    /// One field, by its index in that order (LR12.2).
    GetField {
        object: Value,
        field: u32,
    },
    /// Writing one field of a mutable struct (LR59).
    SetField {
        object: Value,
        field: u32,
        value: Value,
    },

    /// An enum value: which variant, and what that variant carries (LR15.3).
    MakeEnum {
        ty: Ty,
        variant: u32,
        payload: Vec<Value>,
    },
    /// Which variant a value holds, as the integer a `Switch` reads (LR16).
    GetTag {
        value: Value,
    },
    /// One field of a payload, where the tag has already proved the variant.
    GetPayload {
        value: Value,
        variant: u32,
        field: u32,
    },

    MakeTuple(Vec<Value>),
    /// One member of a tuple, by position (LR14).
    GetElement {
        tuple: Value,
        index: u32,
    },

    /// `[a, b]`, `Map { ... }`, `Set { ... }` (LR13).
    MakeList {
        element: Ty,
        values: Vec<Value>,
    },
    MakeMap {
        key: Ty,
        value: Ty,
        entries: Vec<(Value, Value)>,
    },
    MakeSet {
        element: Ty,
        values: Vec<Value>,
    },
    /// A view over the elements selected by an ascending range (LR38).
    MakeSlice {
        receiver: Value,
        range: Value,
        inclusive: bool,
    },
    /// The same view, or nothing where the range is out of bounds (LR38).
    MakeCheckedSlice {
        receiver: Value,
        range: Value,
        inclusive: bool,
    },
    KeepAlive {
        value: Value,
    },
    /// Ends a lexical slice borrow before its value becomes unreachable (LR38).
    ReleaseSlice {
        value: Value,
    },
    ListPush {
        receiver: Value,
        value: Value,
    },
    /// The last element, taken off the list, or nothing (LR13.1).
    ListPop {
        receiver: Value,
    },
    SetInsert {
        receiver: Value,
        value: Value,
    },
    /// Every element taken out of a list, a map, or a set (LR13).
    Clear {
        receiver: Value,
    },
    /// The value at `key`, taken out of the map, or nothing (LR13.2).
    MapRemove {
        receiver: Value,
        key: Value,
    },
    /// Whether the set held `value`, which it no longer does (LR13.3).
    SetRemove {
        receiver: Value,
        value: Value,
    },
    /// Whether a map holds the key `value` (LR13.2), or a set holds it (LR13.3).
    Contains {
        receiver: Value,
        value: Value,
    },

    /// `x:wrappingAdd(y)` and its kin (LR4.3). `Check` produces an optional
    /// of the operand type, and the other modes produce the operand type.
    Overflowing {
        mode: Overflow,
        op: BinaryOp,
        left: Value,
        right: Value,
    },

    /// How many elements a collection holds (LR13).
    Length {
        receiver: Value,
    },
    /// How many buckets a map or a set has, occupied or not (LR13.2, LR13.3).
    /// `Occupied`, `EntryKey`, and `EntryValue` read one bucket by its index
    /// below that count, which is how a loop over one visits every entry
    /// once (LR10.5).
    Buckets {
        receiver: Value,
    },
    Occupied {
        receiver: Value,
        index: Value,
    },
    EntryKey {
        receiver: Value,
        index: Value,
    },
    EntryValue {
        receiver: Value,
        index: Value,
    },

    /// `x[i]` and `x[i] = v` (LR37). The index is checked against what the
    /// container holds unless a pass proves it in range (LR70).
    GetIndex {
        receiver: Value,
        index: Value,
    },
    /// An index whose bounds a whole-function pass proved (LR70).
    GetUncheckedIndex {
        receiver: Value,
        index: Value,
    },
    /// A non-trapping collection lookup returning an optional (LR69, LR70).
    GetCheckedIndex {
        receiver: Value,
        index: Value,
    },
    SetIndex {
        receiver: Value,
        index: Value,
        value: Value,
    },
    SetUncheckedIndex {
        receiver: Value,
        index: Value,
        value: Value,
    },

    /// A present optional, from the value inside it (LR8).
    MakeSome {
        value: Value,
    },
    /// Whether an optional holds a value, which is what `~= nil` asks (LR8).
    IsSome {
        value: Value,
    },
    /// The value inside, where a check has already proved it is there
    /// (LR8, LR57).
    Unwrap {
        value: Value,
    },

    /// The address of a stack slot, which `&x` and `&mut x` take (LR72).
    AddressOf {
        mutable: bool,
        slot: SlotId,
    },
    /// The address of stored field `field` of the aggregate `object` points
    /// at, which `&x.f` and `&mut x.f` take (LR72).
    FieldAddress {
        mutable: bool,
        object: Value,
        field: u32,
    },
    /// `pointer` moved `count` values of its target forward, which
    /// `p:add(n)` does (LR72).
    Offset {
        pointer: Value,
        count: Value,
    },
    /// Reading and writing through a pointer, both of which need `unsafe`
    /// (LR29.2, LR72).
    Load {
        pointer: Value,
    },
    Store {
        pointer: Value,
        value: Value,
    },

    /// Reading and writing a stack slot, which a binding whose address is
    /// taken lives in rather than in a value (LR72).
    SlotGet {
        slot: SlotId,
    },
    SlotSet {
        slot: SlotId,
        value: Value,
    },
}

impl InstKind {
    /// What the instruction does besides producing its result (LR55).
    #[must_use]
    pub fn effect(&self) -> Effect {
        match self {
            Self::Const(_)
            | Self::Unary { .. }
            | Self::HashValue { .. }
            | Self::HashCombine { .. }
            | Self::DisplayValue { .. }
            | Self::MakeError { .. }
            | Self::Convert { .. }
            | Self::Reinterpret { .. }
            | Self::IsType { .. }
            | Self::MakeClosure { .. }
            | Self::CopyValue { .. }
            | Self::Freeze { .. }
            | Self::MakeStruct { .. }
            | Self::GetField { .. }
            | Self::MakeEnum { .. }
            | Self::GetTag { .. }
            | Self::GetPayload { .. }
            | Self::MakeTuple(_)
            | Self::GetElement { .. }
            | Self::MakeList { .. }
            | Self::MakeMap { .. }
            | Self::MakeSet { .. }
            | Self::GetCheckedIndex { .. }
            | Self::Contains { .. }
            | Self::MakeSome { .. }
            | Self::IsSome { .. }
            | Self::Unwrap { .. }
            | Self::MakeDyn { .. }
            | Self::DynValue { .. }
            | Self::KeepAlive { .. }
            | Self::AddressOf { .. }
            | Self::FieldAddress { .. }
            | Self::Offset { .. }
            | Self::Overflowing { .. } => Effect::None,

            Self::Binary { op, .. } => {
                if op.can_trap() {
                    Effect::Trap
                } else {
                    Effect::None
                }
            }
            Self::GetIndex { .. } | Self::MakeSlice { .. } => Effect::Trap,
            Self::MakeCheckedSlice { .. } => Effect::None,
            Self::Assert { .. } | Self::Panic { .. } => Effect::Trap,

            Self::Call { .. }
            | Self::CallIndirect { .. }
            | Self::CallVirtual { .. }
            | Self::SetField { .. }
            | Self::SetIndex { .. }
            | Self::SetUncheckedIndex { .. }
            | Self::GetUncheckedIndex { .. }
            | Self::ListPush { .. }
            | Self::ListPop { .. }
            | Self::SetInsert { .. }
            | Self::MapRemove { .. }
            | Self::SetRemove { .. }
            | Self::Clear { .. }
            | Self::ReleaseSlice { .. }
            | Self::Length { .. }
            | Self::Buckets { .. }
            | Self::Occupied { .. }
            | Self::EntryKey { .. }
            | Self::EntryValue { .. }
            | Self::Load { .. }
            | Self::Store { .. }
            | Self::SlotGet { .. }
            | Self::SlotSet { .. } => Effect::State,
            Self::Print { .. } => Effect::State,
        }
    }
}

/// A jump, and the values it passes to the block it lands in.
#[derive(Debug, Clone, PartialEq)]
pub struct Target {
    pub block: BlockId,
    /// One per parameter of the target block, in order.
    pub args: Vec<Value>,
}

impl Target {
    #[must_use]
    pub fn new(block: BlockId, args: Vec<Value>) -> Self {
        Self { block, args }
    }

    /// A jump to a block that takes no parameters.
    #[must_use]
    pub fn to(block: BlockId) -> Self {
        Self {
            block,
            args: Vec::new(),
        }
    }
}

/// What ends a block. Every block has exactly one.
#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    Jump(Target),
    Branch {
        condition: Value,
        then: Target,
        otherwise: Target,
    },
    /// A jump chosen by an integer, which is how a `match` over an enum's tag
    /// leaves its block (LR16).
    Switch {
        value: Value,
        /// In ascending order of the tag they match, so a reader can find one
        /// without scanning.
        cases: Vec<(u64, Target)>,
        default: Target,
    },
    /// Leaving the function. A function with no result returns a value of
    /// [`Ty::Unit`], so there is always one (LR9.1).
    Return(Value),
    Trap(Trap),
}

impl Terminator {
    /// Every block this one can reach, in the order it names them.
    pub fn targets(&self) -> impl Iterator<Item = &Target> {
        let (first, second, rest): (_, _, &[(u64, Target)]) = match self {
            Self::Jump(target) => (Some(target), None, &[]),
            Self::Branch {
                then, otherwise, ..
            } => (Some(then), Some(otherwise), &[]),
            Self::Switch { cases, default, .. } => (Some(default), None, cases.as_slice()),
            Self::Return(_) | Self::Trap(_) => (None, None, &[]),
        };
        first
            .into_iter()
            .chain(second)
            .chain(rest.iter().map(|(_, target)| target))
    }
}
