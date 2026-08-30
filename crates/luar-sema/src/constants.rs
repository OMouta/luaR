//! Module-level `const` values, worked out before anything reads them
//! (LR24, LR79).

use std::collections::HashMap;

use luar_ast::{
    BinaryOp, Binding, Expr, ExprKind, InterpolationPart, Item, StmtKind, TypeKind, UnaryOp,
};

use crate::modules::{Graph, ModuleId};
use crate::names::{Names, Origin};
use crate::table::{Kind, Kinds};
use crate::types::{Primitive, Type};

/// A value worked out while compiling (LR79).
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Nil,
    Bool(bool),
    /// An integer, and the type it was written at, where one was. A literal
    /// takes the type context asks for (LR39).
    Int(i128, Option<Primitive>),
    Float(f64),
    Char(char),
    Str(String),
    Bytes(Vec<u8>),
    Tuple(Vec<Value>),
    Record(Vec<(String, Value)>),
    /// A struct, or a variant of an enum, with what it carries.
    Named {
        module: ModuleId,
        name: String,
        variant: Option<String>,
        payload: Payload,
    },
}

/// What a struct or a variant carries (LR15.2).
#[derive(Debug, Clone, PartialEq)]
pub enum Payload {
    Unit,
    Tuple(Vec<Value>),
    Record(Vec<(String, Value)>),
}

/// Every module-level `const` that could be worked out, by module and name.
pub type Constants = HashMap<(ModuleId, String), Value>;

impl Value {
    /// The type the value has, with no arguments on a generic type; those are
    /// filled in once the declaration is readable (LR19).
    #[must_use]
    pub fn type_of(&self) -> Type {
        match self {
            Self::Nil => Type::Primitive(Primitive::Nil),
            Self::Bool(_) => Type::BOOL,
            Self::Int(_, written) => Type::Primitive(written.unwrap_or(Primitive::I64)),
            Self::Float(_) => Type::Primitive(Primitive::F64),
            Self::Char(_) => Type::Primitive(Primitive::Char),
            Self::Str(_) => Type::STRING,
            Self::Bytes(_) => Type::Primitive(Primitive::Bytes),
            Self::Tuple(items) => Type::Tuple(items.iter().map(Self::type_of).collect()),
            Self::Record(fields) => Type::Record(
                fields
                    .iter()
                    .map(|(name, value)| (name.clone(), value.type_of()))
                    .collect(),
            ),
            Self::Named { module, name, .. } => Type::Named {
                module: *module,
                name: name.clone(),
                args: Vec::new(),
            },
        }
    }

    /// The value as an array length or another count (LR71).
    #[must_use]
    pub fn integer(&self) -> Option<u64> {
        match self {
            Self::Int(value, _) => u64::try_from(*value).ok(),
            _ => None,
        }
    }
}

/// Works out every module-level `const` whose initializer is in the pure
/// subset and reads only other constants, in whatever order the modules and
/// the constants are written (LR24).
#[must_use]
pub fn evaluate(graph: &Graph, names: &Names, kinds: &Kinds) -> Constants {
    let mut values = Constants::new();

    loop {
        let mut found = Vec::new();
        for (module, node) in graph.modules() {
            let evaluator = Evaluator {
                names,
                kinds,
                module,
                values: &values,
            };
            each_constant(&node.ast.items, &mut |name, written, value| {
                if values.contains_key(&(module, name.to_owned())) {
                    return;
                }
                if let Some(value) = evaluator.constant(written, value) {
                    found.push(((module, name.to_owned()), value));
                }
            });
        }

        if found.is_empty() {
            return values;
        }
        values.extend(found);
    }
}

/// Puts `Unresolved` where a generic type read from a value has no arguments
/// yet, `params` giving how many each type takes (LR19).
#[must_use]
pub fn fill_args(ty: &Type, params: &HashMap<(ModuleId, String), usize>) -> Type {
    match ty {
        Type::Named { module, name, args } if args.is_empty() => {
            let count = params
                .get(&(*module, name.clone()))
                .copied()
                .unwrap_or_default();
            Type::Named {
                module: *module,
                name: name.clone(),
                args: vec![Type::Unresolved; count],
            }
        }
        Type::Tuple(items) => {
            Type::Tuple(items.iter().map(|item| fill_args(item, params)).collect())
        }
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), fill_args(ty, params)))
                .collect(),
        ),
        other => other.clone(),
    }
}

/// Every module-level `const` bound to one name, under `#if` or not.
fn each_constant(items: &[Item], f: &mut impl FnMut(&str, Option<&luar_ast::Type>, &Expr)) {
    for item in items {
        match item {
            Item::Stmt(stmt) => {
                if let StmtKind::Const {
                    binding: Binding::Name(name),
                    ty,
                    value,
                    ..
                } = &stmt.kind
                {
                    f(name, ty.as_ref(), value);
                }
            }
            Item::Conditional(conditional) => {
                for (_, items) in &conditional.branches {
                    each_constant(items, f);
                }
                if let Some(items) = &conditional.otherwise {
                    each_constant(items, f);
                }
            }
            _ => {}
        }
    }
}

struct Evaluator<'a> {
    names: &'a Names,
    kinds: &'a Kinds,
    module: ModuleId,
    values: &'a Constants,
}

impl Evaluator<'_> {
    /// The value of one `const`, with an integer taking the type written
    /// beside it (LR39).
    fn constant(&self, written: Option<&luar_ast::Type>, value: &Expr) -> Option<Value> {
        let value = self.expr(value)?;
        match (value, written.and_then(primitive)) {
            (Value::Int(value, None), Some(ty)) if ty.is_integer() => {
                Some(Value::Int(value, Some(ty)))
            }
            (value, _) => Some(value),
        }
    }

    fn expr(&self, expr: &Expr) -> Option<Value> {
        match &expr.kind {
            ExprKind::Nil => Some(Value::Nil),
            ExprKind::Bool(value) => Some(Value::Bool(*value)),
            ExprKind::Integer(value) => Some(Value::Int(i128::from(*value), None)),
            ExprKind::Float(value) => Some(Value::Float(*value)),
            ExprKind::Char(value) => Some(Value::Char(*value)),
            ExprKind::String(text) => Some(Value::Str(text.clone())),
            ExprKind::ByteString(bytes) => Some(Value::Bytes(bytes.clone())),
            ExprKind::Interpolation(parts) => {
                let mut text = String::new();
                for part in parts {
                    match part {
                        InterpolationPart::Text(literal) => text.push_str(literal),
                        InterpolationPart::Expr(expr) => {
                            text.push_str(&display(&self.expr(expr)?)?)
                        }
                    }
                }
                Some(Value::Str(text))
            }
            ExprKind::Name(name) => self.named(name),
            ExprKind::Unary { op, operand } => {
                let operand = self.expr(operand)?;
                match (op, operand) {
                    (UnaryOp::Negate, Value::Int(value, ty)) => {
                        Some(Value::Int(value.checked_neg()?, ty))
                    }
                    (UnaryOp::Negate, Value::Float(value)) => Some(Value::Float(-value)),
                    (UnaryOp::Not, Value::Bool(value)) => Some(Value::Bool(!value)),
                    (UnaryOp::BitNot, Value::Int(value, ty)) => Some(Value::Int(!value, ty)),
                    _ => None,
                }
            }
            ExprKind::Binary {
                op, left, right, ..
            } => {
                let left = self.expr(left)?;
                let right = self.expr(right)?;
                binary(*op, left, right)
            }
            // LR33: `as` converts between numeric types.
            ExprKind::Cast { value, ty } => {
                let value = self.expr(value)?;
                let target = primitive(ty)?;
                match value {
                    Value::Int(value, _) if target.is_integer() => {
                        Some(Value::Int(value, Some(target)))
                    }
                    Value::Int(value, _) if target.is_float() => Some(Value::Float(value as f64)),
                    Value::Float(value) if target.is_float() => Some(Value::Float(value)),
                    Value::Float(value) if target.is_integer() => {
                        Some(Value::Int(value as i128, Some(target)))
                    }
                    _ => None,
                }
            }
            ExprKind::Tuple(items) => Some(Value::Tuple(
                items
                    .iter()
                    .map(|item| self.expr(item))
                    .collect::<Option<Vec<_>>>()?,
            )),
            ExprKind::Record { path, fields } => {
                let fields = fields
                    .iter()
                    .map(|field| Some((field.name.clone(), self.expr(&field.value)?)))
                    .collect::<Option<Vec<_>>>()?;
                if path.is_empty() {
                    return Some(Value::Record(fields));
                }
                let (module, name, variant) = self.type_path(path)?;
                Some(Value::Named {
                    module,
                    name,
                    variant,
                    payload: Payload::Record(fields),
                })
            }
            // LR15.3: a variant is reached through its enum.
            ExprKind::Field {
                receiver,
                name,
                optional: false,
            } => {
                let (module, enumeration) = self.enumeration(receiver)?;
                Some(Value::Named {
                    module,
                    name: enumeration,
                    variant: Some(name.clone()),
                    payload: Payload::Unit,
                })
            }
            ExprKind::Call {
                callee,
                method: None,
                type_args,
                args,
            } if type_args.is_empty() => {
                let ExprKind::Field {
                    receiver,
                    name,
                    optional: false,
                } = &callee.kind
                else {
                    return None;
                };
                let (module, enumeration) = self.enumeration(receiver)?;
                let payload = args
                    .iter()
                    .map(|argument| {
                        argument
                            .name
                            .is_none()
                            .then(|| self.expr(&argument.value))?
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(Value::Named {
                    module,
                    name: enumeration,
                    variant: Some(name.clone()),
                    payload: Payload::Tuple(payload),
                })
            }
            _ => None,
        }
    }

    /// What a name reads: another `const` of this module, or one imported
    /// (LR21.1, LR24).
    fn named(&self, name: &str) -> Option<Value> {
        let key = match &self.names.scope(self.module).get(name)?.origin {
            Origin::Binding { constant: true, .. } => (self.module, name.to_owned()),
            Origin::Imported { module, name } => (*module, name.clone()),
            _ => return None,
        };
        self.values.get(&key).cloned()
    }

    /// The enum a receiver names, written plainly or through a namespace.
    fn enumeration(&self, receiver: &Expr) -> Option<(ModuleId, String)> {
        let path: Vec<String> = match &receiver.kind {
            ExprKind::Name(name) => vec![name.clone()],
            ExprKind::Field {
                receiver,
                name,
                optional: false,
            } => match &receiver.kind {
                ExprKind::Name(namespace) => vec![namespace.clone(), name.clone()],
                _ => return None,
            },
            _ => return None,
        };
        let (module, name) = self.declaration(&path)?;
        (self.kinds.get(module, &name) == Some(Kind::Enum)).then_some((module, name))
    }

    /// The struct a path names, or the enum and the variant.
    fn type_path(&self, path: &[String]) -> Option<(ModuleId, String, Option<String>)> {
        if let Some((module, name)) = self.declaration(path)
            && self.kinds.get(module, &name) == Some(Kind::Struct)
        {
            return Some((module, name, None));
        }
        let (variant, prefix) = path.split_last()?;
        let (module, name) = self.declaration(prefix)?;
        (self.kinds.get(module, &name) == Some(Kind::Enum))
            .then(|| (module, name, Some(variant.clone())))
    }

    /// The declaration a path names, of this module or another (LR21.1).
    fn declaration(&self, path: &[String]) -> Option<(ModuleId, String)> {
        let first = path.first()?;
        match (
            &self.names.scope(self.module).get(first)?.origin,
            path.len(),
        ) {
            (Origin::Declared { .. }, 1) => Some((self.module, first.clone())),
            (Origin::Imported { module, name }, 1) => Some((*module, name.clone())),
            (Origin::Namespace(module), 2) => Some((*module, path[1].clone())),
            _ => None,
        }
    }
}

/// The primitive a written type names, if it names one.
fn primitive(ty: &luar_ast::Type) -> Option<Primitive> {
    match &ty.kind {
        TypeKind::Path { segments, args } if args.is_empty() && segments.len() == 1 => {
            Primitive::from_name(&segments[0])
        }
        _ => None,
    }
}

/// How a value reads inside an interpolated string (LR4.6).
fn display(value: &Value) -> Option<String> {
    match value {
        Value::Bool(value) => Some(value.to_string()),
        Value::Int(value, _) => Some(value.to_string()),
        Value::Char(value) => Some(value.to_string()),
        Value::Str(text) => Some(text.clone()),
        _ => None,
    }
}

/// The type two integer operands agree on: the written one where either has
/// one (LR39).
fn agreed(left: Option<Primitive>, right: Option<Primitive>) -> Option<Option<Primitive>> {
    match (left, right) {
        (Some(left), Some(right)) if left != right => None,
        (Some(ty), _) | (_, Some(ty)) => Some(Some(ty)),
        (None, None) => Some(None),
    }
}

fn binary(op: BinaryOp, left: Value, right: Value) -> Option<Value> {
    match (left, right) {
        (Value::Int(left, left_ty), Value::Int(right, right_ty)) => {
            let ty = agreed(left_ty, right_ty)?;
            let int = |value: Option<i128>| value.map(|value| Value::Int(value, ty));
            let shift = |value: i128| u32::try_from(value).ok();
            match op {
                BinaryOp::Add => int(left.checked_add(right)),
                BinaryOp::Subtract => int(left.checked_sub(right)),
                BinaryOp::Multiply => int(left.checked_mul(right)),
                BinaryOp::IntegerDivide => int(left.checked_div(right)),
                BinaryOp::Remainder => int(left.checked_rem(right)),
                BinaryOp::Power => int(left.checked_pow(shift(right)?)),
                BinaryOp::BitAnd => int(Some(left & right)),
                BinaryOp::BitOr => int(Some(left | right)),
                BinaryOp::BitXor => int(Some(left ^ right)),
                BinaryOp::ShiftLeft => int(left.checked_shl(shift(right)?)),
                BinaryOp::ShiftRight => int(left.checked_shr(shift(right)?)),
                BinaryOp::Equal => Some(Value::Bool(left == right)),
                BinaryOp::NotEqual => Some(Value::Bool(left != right)),
                BinaryOp::Less => Some(Value::Bool(left < right)),
                BinaryOp::LessEqual => Some(Value::Bool(left <= right)),
                BinaryOp::Greater => Some(Value::Bool(left > right)),
                BinaryOp::GreaterEqual => Some(Value::Bool(left >= right)),
                _ => None,
            }
        }
        (Value::Float(left), Value::Float(right)) => match op {
            BinaryOp::Add => Some(Value::Float(left + right)),
            BinaryOp::Subtract => Some(Value::Float(left - right)),
            BinaryOp::Multiply => Some(Value::Float(left * right)),
            BinaryOp::Divide => Some(Value::Float(left / right)),
            BinaryOp::Power => Some(Value::Float(left.powf(right))),
            BinaryOp::Equal => Some(Value::Bool(left == right)),
            BinaryOp::NotEqual => Some(Value::Bool(left != right)),
            BinaryOp::Less => Some(Value::Bool(left < right)),
            BinaryOp::LessEqual => Some(Value::Bool(left <= right)),
            BinaryOp::Greater => Some(Value::Bool(left > right)),
            BinaryOp::GreaterEqual => Some(Value::Bool(left >= right)),
            _ => None,
        },
        (Value::Bool(left), Value::Bool(right)) => match op {
            BinaryOp::And => Some(Value::Bool(left && right)),
            BinaryOp::Or => Some(Value::Bool(left || right)),
            BinaryOp::Equal => Some(Value::Bool(left == right)),
            BinaryOp::NotEqual => Some(Value::Bool(left != right)),
            _ => None,
        },
        (Value::Str(left), Value::Str(right)) => match op {
            BinaryOp::Concat => Some(Value::Str(left + &right)),
            BinaryOp::Equal => Some(Value::Bool(left == right)),
            BinaryOp::NotEqual => Some(Value::Bool(left != right)),
            _ => None,
        },
        (Value::Char(left), Value::Char(right)) => match op {
            BinaryOp::Equal => Some(Value::Bool(left == right)),
            BinaryOp::NotEqual => Some(Value::Bool(left != right)),
            BinaryOp::Less => Some(Value::Bool(left < right)),
            BinaryOp::LessEqual => Some(Value::Bool(left <= right)),
            BinaryOp::Greater => Some(Value::Bool(left > right)),
            BinaryOp::GreaterEqual => Some(Value::Bool(left >= right)),
            _ => None,
        },
        _ => None,
    }
}
