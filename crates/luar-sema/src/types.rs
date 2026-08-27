//! The types a LuaR program is written in, and when one accepts another
//! (LR6, LR4.3, LR39).

use std::fmt;

use crate::modules::ModuleId;

/// A primitive type (LR6).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Primitive {
    Nil,
    Bool,
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
    F32,
    F64,
    String,
    Bytes,
    Char,
    Never,
    Any,
    Unknown,
}

impl Primitive {
    /// The primitive `name` spells, if it spells one.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        let primitive = match name {
            "nil" => Self::Nil,
            "bool" => Self::Bool,
            "i8" => Self::I8,
            "i16" => Self::I16,
            "i32" => Self::I32,
            "i64" | "int" => Self::I64,
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" | "uint" => Self::U64,
            "isize" => Self::Isize,
            "usize" => Self::Usize,
            "f32" => Self::F32,
            "f64" | "float" => Self::F64,
            "string" => Self::String,
            "bytes" => Self::Bytes,
            "char" => Self::Char,
            "never" => Self::Never,
            "any" => Self::Any,
            "unknown" => Self::Unknown,
            _ => return None,
        };
        Some(primitive)
    }

    /// How a diagnostic spells it. `int` reads as `int` rather than `i64`,
    /// because that is the name the spec gives the default (LR4.3).
    #[must_use]
    pub fn spelling(self) -> &'static str {
        match self {
            Self::Nil => "nil",
            Self::Bool => "bool",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "int",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "uint",
            Self::Isize => "isize",
            Self::Usize => "usize",
            Self::F32 => "f32",
            Self::F64 => "float",
            Self::String => "string",
            Self::Bytes => "bytes",
            Self::Char => "char",
            Self::Never => "never",
            Self::Any => "any",
            Self::Unknown => "unknown",
        }
    }

    /// Whether this is one of the integer types (LR4.3).
    #[must_use]
    pub fn is_integer(self) -> bool {
        matches!(
            self,
            Self::I8
                | Self::I16
                | Self::I32
                | Self::I64
                | Self::U8
                | Self::U16
                | Self::U32
                | Self::U64
                | Self::Isize
                | Self::Usize
        )
    }

    /// Whether this is one of the floating-point types (LR4.4).
    #[must_use]
    pub fn is_float(self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }

    /// Whether `value` is representable, which is what makes an integer
    /// literal polymorphic (LR39).
    #[must_use]
    pub fn holds(self, value: u64) -> bool {
        let limit = match self {
            Self::I8 => i8::MAX as u64,
            Self::I16 => i16::MAX as u64,
            Self::I32 => i32::MAX as u64,
            // `isize` is pointer-sized and never wider than 64 bits, so what
            // fits `i64` is the most that can be promised for it.
            Self::I64 | Self::Isize => i64::MAX as u64,
            Self::U8 => u8::MAX as u64,
            Self::U16 => u16::MAX as u64,
            Self::U32 => u32::MAX as u64,
            Self::U64 | Self::Usize => u64::MAX,
            // In a floating-point position, a literal fits when it survives
            // the round trip.
            Self::F32 => return value as f32 as u64 == value,
            Self::F64 => return value as f64 as u64 == value,
            _ => return false,
        };
        value <= limit
    }
}

/// A generic type the language names without an import (LR54.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Builtin {
    /// `Result<T, E>`, the type of every fallible signature (LR25.1).
    Result,
    /// The collections `[...]` and `Map { ... }` build (LR13).
    List,
    Map,
    Set,
    /// What freezing one returns (LR59).
    FrozenList,
    FrozenMap,
    FrozenSet,
    /// `Task<T>`, what calling an async function produces (LR27).
    Task,
}

impl Builtin {
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        let builtin = match name {
            "Result" => Self::Result,
            "List" => Self::List,
            "Map" => Self::Map,
            "Set" => Self::Set,
            "FrozenList" => Self::FrozenList,
            "FrozenMap" => Self::FrozenMap,
            "FrozenSet" => Self::FrozenSet,
            "Task" => Self::Task,
            _ => return None,
        };
        Some(builtin)
    }

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
            Self::Task => "Task",
        }
    }
}

/// A type, as the checker holds it.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Primitive(Primitive),
    /// `Result<T, E>` and the collections (LR54.1).
    Builtin {
        kind: Builtin,
        args: Vec<Type>,
    },
    /// A struct, enum, interface, or alias, and the module declaring it.
    Named {
        module: ModuleId,
        name: String,
        args: Vec<Type>,
    },
    /// A type parameter of the enclosing declaration (LR19).
    Parameter(String),
    /// `T?` (LR8).
    Optional(Box<Type>),
    Union(Vec<Type>),
    Intersection(Vec<Type>),
    Tuple(Vec<Type>),
    Function {
        asynchronous: bool,
        sendable: bool,
        params: Vec<Type>,
        result: Box<Type>,
    },
    /// `[T; N]` (LR71). The length is a constant expression, so comparing
    /// lengths waits for `const` evaluation (LR24).
    Array(Box<Type>),
    Pointer {
        mutable: bool,
        target: Box<Type>,
    },
    /// A structural record, by field name (LR12.1).
    Record(Vec<(String, Type)>),
    /// An integer literal, before context gives it a type (LR39).
    IntegerLiteral(u64),
    /// A floating-point literal, before context gives it a type (LR39).
    FloatLiteral,
    /// `[...]`, and what its elements hold, before context says which
    /// sequence it fills: a `List<T>` or a fixed-size array (LR13.1, LR71).
    SequenceLiteral(Box<Type>),
    /// A type this stage does not know: either it was reported already, or
    /// working it out needs a stage that does not exist yet. It accepts
    /// everything and everything accepts it, so it causes no diagnostic.
    Unresolved,
}

impl Type {
    pub const BOOL: Self = Self::Primitive(Primitive::Bool);
    pub const STRING: Self = Self::Primitive(Primitive::String);

    /// Whether a value of type `value` may be used where `self` is wanted.
    #[must_use]
    pub fn without_nil(&self) -> Self {
        match self {
            Self::Optional(inner) => inner.as_ref().clone(),
            Self::Union(members) => {
                let kept: Vec<Self> = members
                    .iter()
                    .filter(|member| !matches!(member, Self::Primitive(Primitive::Nil)))
                    .cloned()
                    .collect();

                match kept.len() {
                    1 => kept.into_iter().next().expect("one member"),
                    _ => Self::Union(kept),
                }
            }
            other => other.clone(),
        }
    }

    /// This type with `taken` removed from it, which is what a value has
    /// where an `is` test did not hold (LR17.2, LR57).
    #[must_use]
    pub fn without(&self, taken: &Self) -> Self {
        let Self::Union(members) = self else {
            return self.clone();
        };

        let kept: Vec<Self> = members
            .iter()
            .filter(|member| *member != taken)
            .cloned()
            .collect();

        match kept.len() {
            1 => kept.into_iter().next().expect("one member"),
            _ => Self::Union(kept),
        }
    }

    /// This type made optional, unless it already is. An optional chain gives
    /// one absent value however long the chain is, not one per link (LR8).
    #[must_use]
    pub fn optional(self) -> Self {
        if self.is_optional() {
            self
        } else {
            Self::Optional(Box::new(self))
        }
    }

    /// Whether `nil` inhabits this type, which is what makes it optional
    /// however it is written (LR8).
    #[must_use]
    pub fn is_optional(&self) -> bool {
        match self {
            Self::Optional(_) => true,
            Self::Union(members) => members
                .iter()
                .any(|member| matches!(member, Self::Primitive(Primitive::Nil))),
            _ => false,
        }
    }

    /// Answers yes wherever it is unsure, so that reporting `!accepts` reports
    /// only what is definitely wrong.
    #[must_use]
    pub fn accepts(&self, value: &Self) -> bool {
        // `unknown` is the top type and holds anything; what it does not do is
        // go anywhere else without a check first (LR6.3).
        if matches!(self, Self::Primitive(Primitive::Unknown)) {
            return true;
        }

        // `any` opts out of checking (LR6.4), `never` reaches no use at all
        // (LR6.2), and `Unresolved` is the compiler saying it does not know.
        if matches!(self, Self::Unresolved | Self::Primitive(Primitive::Any))
            || matches!(
                value,
                Self::Unresolved | Self::Primitive(Primitive::Any | Primitive::Never)
            )
        {
            return true;
        }

        match (self, value) {
            // A literal takes the type context asks for, where the value fits
            // (LR39).
            (Self::Primitive(target), Self::IntegerLiteral(literal)) => target.holds(*literal),
            (Self::Primitive(target), Self::FloatLiteral) => target.is_float(),

            // A bracket literal fills either sequence (LR13.1, LR71).
            (Self::Array(element), Self::SequenceLiteral(held)) => element.accepts(held),
            (
                Self::Builtin {
                    kind: Builtin::List | Builtin::FrozenList,
                    args,
                },
                Self::SequenceLiteral(held),
            ) => args.first().is_none_or(|element| element.accepts(held)),

            // `nil` inhabits every optional, and nothing else (LR8).
            (Self::Optional(_), Self::Primitive(Primitive::Nil)) => true,
            (Self::Optional(inner), Self::Optional(held)) => inner.accepts(held),
            (Self::Optional(inner), _) => inner.accepts(value),

            // A union holds any of its members (LR17.2).
            (Self::Union(members), _) => members.iter().any(|member| member.accepts(value)),
            (_, Self::Union(members)) => members.iter().all(|member| self.accepts(member)),

            (Self::Primitive(target), Self::Primitive(held)) => target == held,
            (
                Self::Builtin { kind, args },
                Self::Builtin {
                    kind: held_kind,
                    args: held,
                },
            ) => kind == held_kind && invariant(args, held),
            (
                Self::Named { module, name, args },
                Self::Named {
                    module: held_module,
                    name: held_name,
                    args: held,
                },
            ) => module == held_module && name == held_name && invariant(args, held),
            (Self::Parameter(name), Self::Parameter(held)) => name == held,
            (Self::Tuple(members), Self::Tuple(held)) => {
                members.len() == held.len() && members.iter().zip(held).all(|(m, h)| m.accepts(h))
            }
            (
                Self::Pointer { mutable, target },
                Self::Pointer {
                    mutable: held_mutable,
                    target: held,
                },
            ) => mutable == held_mutable && target.accepts(held),

            // Anything else pairs shapes this stage does not compare yet:
            // functions, records, arrays, intersections, and every mixture of
            // kinds not named above.
            _ => !compared(self) || !compared(value),
        }
    }
}

/// Whether a type is one this stage compares. Anything else is left alone
/// rather than reported, so the checker grows by learning shapes rather than
/// by unlearning wrong answers.
/// LR19: type arguments are invariant, so `Box<int>` is not a `Box<Display>`
/// however `int` and `Display` relate. Each pair has to go both ways.
fn invariant(wanted: &[Type], held: &[Type]) -> bool {
    wanted.len() == held.len()
        && wanted
            .iter()
            .zip(held)
            .all(|(wanted, held)| wanted.accepts(held) && held.accepts(wanted))
}

fn compared(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Primitive(_)
            | Type::Builtin { .. }
            | Type::Named { .. }
            | Type::Parameter(_)
            | Type::Optional(_)
            | Type::Union(_)
            | Type::Tuple(_)
            | Type::Pointer { .. }
            | Type::IntegerLiteral(_)
            | Type::FloatLiteral
            | Type::SequenceLiteral(_)
    )
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Primitive(primitive) => f.write_str(primitive.spelling()),
            Self::Builtin { kind, args } => {
                f.write_str(kind.spelling())?;
                arguments(f, args)
            }
            Self::Named { name, args, .. } => {
                f.write_str(name)?;
                arguments(f, args)
            }
            Self::Parameter(name) => f.write_str(name),
            Self::Optional(inner) => write!(f, "{inner}?"),
            Self::Union(members) => join(f, members, " | "),
            Self::Intersection(members) => join(f, members, " & "),
            Self::Tuple(members) => {
                f.write_str("(")?;
                join(f, members, ", ")?;
                f.write_str(")")
            }
            Self::Function {
                asynchronous,
                sendable: _,
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
            Self::Array(element) => write!(f, "[{element}; N]"),
            Self::Pointer { mutable, target } => {
                let qualifier = if *mutable { "mut" } else { "const" };
                write!(f, "*{qualifier} {target}")
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
            Self::SequenceLiteral(element) => write!(f, "a sequence of `{element}`"),
            Self::IntegerLiteral(_) => f.write_str("an integer literal"),
            Self::FloatLiteral => f.write_str("a float literal"),
            Self::Unresolved => f.write_str("an unknown type"),
        }
    }
}

fn arguments(f: &mut fmt::Formatter<'_>, args: &[Type]) -> fmt::Result {
    if args.is_empty() {
        return Ok(());
    }
    f.write_str("<")?;
    join(f, args, ", ")?;
    f.write_str(">")
}

fn join(f: &mut fmt::Formatter<'_>, types: &[Type], separator: &str) -> fmt::Result {
    for (i, ty) in types.iter().enumerate() {
        if i > 0 {
            f.write_str(separator)?;
        }
        write!(f, "{ty}")?;
    }
    Ok(())
}
