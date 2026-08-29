//! What the checker worked out, kept for the stages after it.

use std::collections::{HashMap, HashSet};

use luar_diagnostics::Span;

use crate::types::Type;

/// An operation the compiler implements: a predeclared one (LR54.1), or one
/// the standard library declares with `@intrinsic` (LR60).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Intrinsic {
    Print,
    Error,
    Identical,
    Assert,
    DebugAssert,
    Panic,
    ListNew,
    MapNew,
    SetNew,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CollectionMutation {
    ListPush,
    ListPop,
    ListInsert,
    ListRemoveAt,
    ListReverse,
    ListPushAll,
    SetInsert,
    MapRemove,
    SetRemove,
    Clear,
}

/// What `x:wrappingAdd(y)` and its kin do where the ordinary operator would
/// trap (LR4.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Overflow {
    Wrap,
    Saturate,
    Check,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OverflowMethod {
    pub mode: Overflow,
    pub op: luar_ast::BinaryOp,
}

impl Intrinsic {
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Print => "print",
            Self::Error => "Error",
            Self::Identical => "identical",
            Self::Assert => "assert",
            Self::DebugAssert => "debugAssert",
            Self::Panic => "panic",
            Self::ListNew => "List.new",
            Self::MapNew => "Map.new",
            Self::SetNew => "Set.new",
        }
    }
}

/// What the checker knows about one program.
#[derive(Debug, Default)]
pub struct Facts {
    types: HashMap<Span, Type>,
    calls: HashMap<Span, Span>,
    bindings: HashMap<Span, Type>,
    type_args: HashMap<Span, Vec<Type>>,
    intrinsics: HashMap<Span, Intrinsic>,
    freezes: HashSet<Span>,
    checked_indexes: HashSet<Span>,
    contains: HashSet<Span>,
    index_of: HashSet<Span>,
    ok_or: HashSet<Span>,
    map_err: HashSet<Span>,
    collection_mutations: HashMap<Span, CollectionMutation>,
    overflow_methods: HashMap<Span, OverflowMethod>,
    /// The names something takes the address of (LR72).
    addressed: HashSet<String>,
}

impl Facts {
    /// Records the type of the expression at `span`.
    pub fn record_type(&mut self, span: Span, ty: Type) {
        self.types.insert(span, ty);
    }

    #[must_use]
    pub fn type_of(&self, span: Span) -> Option<&Type> {
        self.types.get(&span)
    }

    /// Records that the call at `span` reached the declaration written at
    /// `declaration` (LR40, LR76).
    pub fn record_call(&mut self, span: Span, declaration: Span) {
        self.calls.insert(span, declaration);
    }

    /// The declaration the call at `span` reached, if the checker settled on
    /// one. A call it could not resolve has no entry, and reported why.
    #[must_use]
    pub fn call(&self, span: Span) -> Option<Span> {
        self.calls.get(&span).copied()
    }

    /// Records the type a binding was declared with, by the span of the
    /// statement declaring it (LR5.1).
    pub fn record_binding(&mut self, span: Span, ty: Type) {
        self.bindings.insert(span, ty);
    }

    #[must_use]
    pub fn binding(&self, span: Span) -> Option<&Type> {
        self.bindings.get(&span)
    }

    /// Records what fills each type parameter of the call at `span`, in the
    /// order the callee declares them (LR19).
    pub fn record_type_args(&mut self, span: Span, args: Vec<Type>) {
        self.type_args.insert(span, args);
    }

    /// What filled the callee's type parameters at `span`, if the call
    /// reached a generic function.
    #[must_use]
    pub fn type_args(&self, span: Span) -> Option<&[Type]> {
        self.type_args.get(&span).map(Vec::as_slice)
    }

    pub fn record_intrinsic(&mut self, span: Span, intrinsic: Intrinsic) {
        self.intrinsics.insert(span, intrinsic);
    }

    #[must_use]
    pub fn intrinsic(&self, span: Span) -> Option<Intrinsic> {
        self.intrinsics.get(&span).copied()
    }

    pub fn record_freeze(&mut self, span: Span) {
        self.freezes.insert(span);
    }

    #[must_use]
    pub fn freezes(&self, span: Span) -> bool {
        self.freezes.contains(&span)
    }

    pub fn record_checked_index(&mut self, span: Span) {
        self.checked_indexes.insert(span);
    }

    #[must_use]
    pub fn checked_index(&self, span: Span) -> bool {
        self.checked_indexes.contains(&span)
    }

    pub fn record_contains(&mut self, span: Span) {
        self.contains.insert(span);
    }

    #[must_use]
    pub fn contains(&self, span: Span) -> bool {
        self.contains.contains(&span)
    }

    pub fn record_index_of(&mut self, span: Span) {
        self.index_of.insert(span);
    }

    #[must_use]
    pub fn index_of(&self, span: Span) -> bool {
        self.index_of.contains(&span)
    }

    pub fn record_ok_or(&mut self, span: Span) {
        self.ok_or.insert(span);
    }

    #[must_use]
    pub fn ok_or(&self, span: Span) -> bool {
        self.ok_or.contains(&span)
    }

    pub fn record_map_err(&mut self, span: Span) {
        self.map_err.insert(span);
    }

    #[must_use]
    pub fn map_err(&self, span: Span) -> bool {
        self.map_err.contains(&span)
    }

    pub fn record_collection_mutation(&mut self, span: Span, mutation: CollectionMutation) {
        self.collection_mutations.insert(span, mutation);
    }

    #[must_use]
    pub fn collection_mutation(&self, span: Span) -> Option<CollectionMutation> {
        self.collection_mutations.get(&span).copied()
    }

    pub fn record_overflow_method(&mut self, span: Span, method: OverflowMethod) {
        self.overflow_methods.insert(span, method);
    }

    #[must_use]
    pub fn overflow_method(&self, span: Span) -> Option<OverflowMethod> {
        self.overflow_methods.get(&span).copied()
    }

    pub fn record_addressed(&mut self, name: String) {
        self.addressed.insert(name);
    }

    /// Whether `&name` or `&mut name` is written anywhere, which is what
    /// makes a binding of that name live in memory (LR72).
    #[must_use]
    pub fn addressed(&self, name: &str) -> bool {
        self.addressed.contains(name)
    }

    /// Takes everything `other` recorded.
    pub fn absorb(&mut self, other: Self) {
        self.types.extend(other.types);
        self.calls.extend(other.calls);
        self.bindings.extend(other.bindings);
        self.type_args.extend(other.type_args);
        self.intrinsics.extend(other.intrinsics);
        self.freezes.extend(other.freezes);
        self.checked_indexes.extend(other.checked_indexes);
        self.contains.extend(other.contains);
        self.index_of.extend(other.index_of);
        self.ok_or.extend(other.ok_or);
        self.map_err.extend(other.map_err);
        self.collection_mutations.extend(other.collection_mutations);
        self.overflow_methods.extend(other.overflow_methods);
        self.addressed.extend(other.addressed);
    }
}
