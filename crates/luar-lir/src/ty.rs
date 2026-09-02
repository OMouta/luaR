//! The types an LIR value carries (LR6).

use std::fmt;

/// A width and a signedness (LR4.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntTy {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    Isize,
    Usize,
}

impl IntTy {
    /// Whether the type is signed, which decides what overflows and how a
    /// shift and a division behave (LR4.3, LR11.1).
    #[must_use]
    pub fn is_signed(self) -> bool {
        matches!(
            self,
            Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::Isize
        )
    }

    /// How wide the type is, or `None` for the two whose width the target
    /// decides.
    #[must_use]
    pub fn bits(self) -> Option<u32> {
        let bits = match self {
            Self::I8 | Self::U8 => 8,
            Self::I16 | Self::U16 => 16,
            Self::I32 | Self::U32 => 32,
            Self::I64 | Self::U64 => 64,
            Self::Isize | Self::Usize => return None,
        };
        Some(bits)
    }

    #[must_use]
    pub fn spelling(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::Isize => "isize",
            Self::Usize => "usize",
        }
    }
}

/// A binary floating-point width (LR4.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatTy {
    F32,
    F64,
}

impl FloatTy {
    #[must_use]
    pub fn bits(self) -> u32 {
        match self {
            Self::F32 => 32,
            Self::F64 => 64,
        }
    }

    #[must_use]
    pub fn spelling(self) -> &'static str {
        match self {
            Self::F32 => "f32",
            Self::F64 => "f64",
        }
    }
}

/// A nominal type declared somewhere in the program: a struct, an enum, or an
/// interface. Indexes the program's type table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeId(pub u32);

/// A generic type the language names without an import (LR54.1), kept apart
/// from user declarations because the backend knows their representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Builtin {
    Result,
    List,
    Map,
    Set,
    FrozenList,
    FrozenMap,
    FrozenSet,
    Slice,
    RangeExclusive,
    RangeInclusive,
    ReversedRangeExclusive,
    ReversedRangeInclusive,
    Task,
}

impl Builtin {
    #[must_use]
    pub fn spelling(self) -> &'static str {
        match self {
            Self::Result => "Result",
            Self::List => "List",
            Self::Map => "Map",
            Self::Set => "Set",
            Self::FrozenList => "FrozenList",
            Self::FrozenMap => "FrozenMap",
            Self::FrozenSet => "FrozenSet",
            Self::Slice => "Slice",
            Self::RangeExclusive => "range",
            Self::RangeInclusive => "range",
            Self::ReversedRangeExclusive => "reversed range",
            Self::ReversedRangeInclusive => "reversed range",
            Self::Task => "Task",
        }
    }
}

/// What an LIR value is made of.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    /// What a function with no declared result gives back (LR9.1). It holds
    /// no information, so the backend gives it no storage.
    Unit,
    /// The type `nil` alone inhabits (LR4.1). A value that may be absent is
    /// an [`Ty::Optional`], not this.
    Nil,
    /// The type no value has (LR6.2). A value carries it where control never
    /// reaches the use, so nothing reads one and it needs no representation.
    Never,
    /// `any` and `unknown` (LR6.3, LR6.4): a value carrying what it is at
    /// runtime, because static type is not what says.
    Dynamic,
    Bool,
    Int(IntTy),
    Float(FloatTy),
    /// One Unicode scalar value (LR6.1).
    Char,
    /// An immutable UTF-8 string (LR4.5).
    Str,
    /// A byte string (LR4.7).
    Bytes,
    /// The common error type, holding its message (LR54.1).
    Error,
    /// A struct, enum, or interface, with its type arguments in the order
    /// they were declared (LR19).
    Named {
        id: TypeId,
        args: Vec<Ty>,
    },
    Builtin {
        kind: Builtin,
        args: Vec<Ty>,
    },
    /// A structural record, by field name in declaration order (LR12.1).
    Record(Vec<(String, Ty)>),
    Tuple(Vec<Ty>),
    /// `T?`: a `T`, or nothing (LR8). Never nested, because a chain of
    /// optional accesses gives one absent value rather than one per link.
    Optional(Box<Ty>),
    /// A value that is one of several types, and carries which (LR17.2).
    Union(Vec<Ty>),
    /// `[T; N]` (LR71).
    Array(Box<Ty>, u64),
    /// `*const T` or `*mut T` (LR72).
    Pointer {
        mutable: bool,
        target: Box<Ty>,
    },
    /// A closure or a function value (LR9.2, LR9.8).
    Function {
        asynchronous: bool,
        params: Vec<Ty>,
        result: Box<Ty>,
    },
    /// The one place a binding lives when a closure captured it and something
    /// assigns to it, which every holder reads and writes (LR9.8).
    Cell(Box<Ty>),
    /// A type parameter of the function or type being lowered (LR19).
    Parameter(String),
}

impl Ty {
    /// `int`, which is `i64` on every target (LR4.3).
    pub const INT: Self = Self::Int(IntTy::I64);

    /// Whether `nil` inhabits the type (LR8).
    #[must_use]
    pub fn is_optional(&self) -> bool {
        matches!(self, Self::Optional(_))
    }

    /// What the type holds when it holds something (LR8). Anything that is
    /// not optional is already that.
    #[must_use]
    pub fn without_optional(self) -> Self {
        match self {
            Self::Optional(inner) => *inner,
            other => other,
        }
    }

    /// This type with each of `params` replaced by the argument filling it
    /// (LR19).
    #[must_use]
    pub fn substitute(&self, params: &[String], args: &[Ty]) -> Self {
        if params.is_empty() {
            return self.clone();
        }

        let each = |types: &[Ty]| -> Vec<Ty> {
            types.iter().map(|ty| ty.substitute(params, args)).collect()
        };

        match self {
            Self::Parameter(name) => match params.iter().position(|param| param == name) {
                Some(index) => args.get(index).cloned().unwrap_or_else(|| self.clone()),
                None => self.clone(),
            },
            Self::Named { id, args: held } => Self::Named {
                id: *id,
                args: each(held),
            },
            Self::Builtin { kind, args: held } => Self::Builtin {
                kind: *kind,
                args: each(held),
            },
            Self::Record(fields) => Self::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), ty.substitute(params, args)))
                    .collect(),
            ),
            Self::Tuple(members) => Self::Tuple(each(members)),
            Self::Union(members) => Self::Union(each(members)),
            Self::Optional(inner) => Self::Optional(Box::new(inner.substitute(params, args))),
            Self::Cell(inner) => Self::Cell(Box::new(inner.substitute(params, args))),
            Self::Array(element, length) => {
                Self::Array(Box::new(element.substitute(params, args)), *length)
            }
            Self::Pointer { mutable, target } => Self::Pointer {
                mutable: *mutable,
                target: Box::new(target.substitute(params, args)),
            },
            Self::Function {
                asynchronous,
                params: takes,
                result,
            } => Self::Function {
                asynchronous: *asynchronous,
                params: each(takes),
                result: Box::new(result.substitute(params, args)),
            },
            other => other.clone(),
        }
    }

    /// Whether the type still mentions a parameter, and so has no layout
    /// until monomorphization has run (LR19).
    #[must_use]
    pub fn is_generic(&self) -> bool {
        match self {
            Self::Parameter(_) => true,
            Self::Named { args, .. } | Self::Builtin { args, .. } | Self::Union(args) => {
                args.iter().any(Self::is_generic)
            }
            Self::Tuple(members) => members.iter().any(Self::is_generic),
            Self::Record(fields) => fields.iter().any(|(_, ty)| ty.is_generic()),
            Self::Optional(inner) | Self::Cell(inner) | Self::Array(inner, _) => inner.is_generic(),
            Self::Pointer { target, .. } => target.is_generic(),
            Self::Function { params, result, .. } => {
                params.iter().any(Self::is_generic) || result.is_generic()
            }
            _ => false,
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => f.write_str("()"),
            Self::Nil => f.write_str("nil"),
            Self::Never => f.write_str("never"),
            Self::Dynamic => f.write_str("dynamic"),
            Self::Bool => f.write_str("bool"),
            Self::Int(int) => f.write_str(int.spelling()),
            Self::Float(float) => f.write_str(float.spelling()),
            Self::Char => f.write_str("char"),
            Self::Str => f.write_str("string"),
            Self::Bytes => f.write_str("bytes"),
            Self::Error => f.write_str("Error"),
            Self::Named { id, args } => {
                write!(f, "type{}", id.0)?;
                arguments(f, args)
            }
            Self::Builtin { kind, args } => {
                f.write_str(kind.spelling())?;
                arguments(f, args)
            }
            Self::Record(fields) => {
                f.write_str("{ ")?;
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{name}: {ty}")?;
                }
                f.write_str(" }")
            }
            Self::Tuple(members) => {
                f.write_str("(")?;
                join(f, members, ", ")?;
                f.write_str(")")
            }
            Self::Optional(inner) => write!(f, "{inner}?"),
            Self::Cell(inner) => write!(f, "cell<{inner}>"),
            Self::Union(members) => join(f, members, " | "),
            Self::Array(element, length) => write!(f, "[{element}; {length}]"),
            Self::Pointer { mutable, target } => {
                let qualifier = if *mutable { "mut" } else { "const" };
                write!(f, "*{qualifier} {target}")
            }
            Self::Function {
                asynchronous,
                params,
                result,
            } => {
                if *asynchronous {
                    f.write_str("async ")?;
                }
                f.write_str("(")?;
                join(f, params, ", ")?;
                write!(f, ") -> {result}")
            }
            Self::Parameter(name) => f.write_str(name),
        }
    }
}

fn arguments(f: &mut fmt::Formatter<'_>, args: &[Ty]) -> fmt::Result {
    if args.is_empty() {
        return Ok(());
    }
    f.write_str("<")?;
    join(f, args, ", ")?;
    f.write_str(">")
}

fn join(f: &mut fmt::Formatter<'_>, types: &[Ty], separator: &str) -> fmt::Result {
    for (i, ty) in types.iter().enumerate() {
        if i > 0 {
            f.write_str(separator)?;
        }
        write!(f, "{ty}")?;
    }
    Ok(())
}
