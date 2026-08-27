//! Writing a program out, for reading.

use std::fmt::Write as _;

use crate::inst::{BinaryOp, Const, Inst, InstKind, Target, Terminator, UnaryOp, Value};
use crate::program::{Function, Nominal, Program, Shape};

/// The whole program: its types, then its functions.
#[must_use]
pub fn program(program: &Program) -> String {
    let mut out = String::new();
    for (_, nominal) in program.types() {
        nominal_to(&mut out, nominal);
        out.push('\n');
    }
    for (id, function) in program.functions() {
        if program.entry == Some(id) {
            out.push_str("entry\n");
        }
        function_to(&mut out, function);
        out.push('\n');
    }
    out
}

/// One function.
#[must_use]
pub fn function(function: &Function) -> String {
    let mut out = String::new();
    function_to(&mut out, function);
    out
}

fn nominal_to(out: &mut String, nominal: &Nominal) {
    let params = if nominal.type_params.is_empty() {
        String::new()
    } else {
        format!("<{}>", nominal.type_params.join(", "))
    };

    match &nominal.shape {
        Shape::Struct(structure) => {
            let kind = if structure.reference {
                "ref struct"
            } else {
                "struct"
            };
            let _ = writeln!(out, "{kind} {}{params}", nominal.name);
            for field in &structure.fields {
                let _ = writeln!(out, "    {}: {}", field.name, field.ty);
            }
        }
        Shape::Enum(enumeration) => {
            let _ = writeln!(out, "enum {}{params}", nominal.name);
            for (tag, variant) in enumeration.variants.iter().enumerate() {
                let fields: Vec<String> = variant
                    .fields
                    .iter()
                    .map(|field| format!("{}: {}", field.name, field.ty))
                    .collect();
                let _ = writeln!(out, "    {tag} {}({})", variant.name, fields.join(", "));
            }
        }
        Shape::Interface(interface) => {
            let _ = writeln!(out, "interface {}{params}", nominal.name);
            for (slot, method) in interface.methods.iter().enumerate() {
                let params: Vec<String> = method.params.iter().map(ToString::to_string).collect();
                let _ = writeln!(
                    out,
                    "    {slot} {}({}) -> {}",
                    method.name,
                    params.join(", "),
                    method.result
                );
            }
            for held in &interface.implementors {
                let methods: Vec<String> = held
                    .methods
                    .iter()
                    .map(|func| format!("func{}", func.0))
                    .collect();
                let _ = writeln!(out, "    impl type{} [{}]", held.ty.0, methods.join(", "));
            }
        }
    }
}

fn function_to(out: &mut String, function: &Function) {
    let params = if function.type_params.is_empty() {
        String::new()
    } else {
        format!("<{}>", function.type_params.join(", "))
    };
    let asynchronous = if function.asynchronous { "async " } else { "" };
    let _ = writeln!(
        out,
        "{asynchronous}function {}{params}({}) -> {}",
        function.name,
        function
            .params
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", "),
        function.result
    );

    for (index, ty) in function.slots().iter().enumerate() {
        let _ = writeln!(out, "    slot{index}: {ty}");
    }

    for (id, block) in function.blocks() {
        let params: Vec<String> = block
            .params
            .iter()
            .map(|value| format!("{}: {}", name(*value), function.type_of(*value)))
            .collect();

        if params.is_empty() {
            let _ = writeln!(out, "  block{}:", id.0);
        } else {
            let _ = writeln!(out, "  block{}({}):", id.0, params.join(", "));
        }

        for inst in &block.insts {
            let _ = writeln!(out, "    {}", instruction(inst, function));
        }
        match &block.term {
            Some(term) => {
                let _ = writeln!(out, "    {}", terminator(term));
            }
            None => {
                let _ = writeln!(out, "    <unterminated>");
            }
        }
    }
}

fn name(value: Value) -> String {
    format!("v{}", value.0)
}

fn list(values: &[Value]) -> String {
    values
        .iter()
        .map(|value| name(*value))
        .collect::<Vec<_>>()
        .join(", ")
}

fn instruction(inst: &Inst, function: &Function) -> String {
    let body = match &inst.kind {
        InstKind::Const(value) => format!("const {}", constant(value)),
        InstKind::Unary { op, operand } => format!("{} {}", unary(*op), name(*operand)),
        InstKind::Binary { op, left, right } => {
            format!("{} {} {}", binary(*op), name(*left), name(*right))
        }
        InstKind::Convert { value, to } => format!("convert {} to {to}", name(*value)),
        InstKind::IsType { value, ty } => format!("is {} {ty}", name(*value)),
        InstKind::Call {
            callee,
            type_args,
            args,
        } => {
            let arguments = if type_args.is_empty() {
                String::new()
            } else {
                format!(
                    "<{}>",
                    type_args
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            format!("call func{}{arguments}({})", callee.0, list(args))
        }
        InstKind::CallIndirect { callee, args } => {
            format!("call {}({})", name(*callee), list(args))
        }
        InstKind::CallVirtual {
            method,
            receiver,
            args,
        } => format!(
            "call virtual type{}#{} {}({})",
            method.interface.0,
            method.slot,
            name(*receiver),
            list(args)
        ),
        InstKind::MakeDyn { interface, value } => match interface {
            Some(interface) => format!("dyn type{} {}", interface.0, name(*value)),
            None => format!("dyn {}", name(*value)),
        },
        InstKind::DynValue { value } => format!("dyn value {}", name(*value)),
        InstKind::MakeClosure { func, captures } => {
            format!("closure func{}[{}]", func.0, list(captures))
        }
        InstKind::CopyValue { value } => format!("copy {}", name(*value)),
        InstKind::MakeStruct { ty, fields } => format!("struct {ty} {{ {} }}", list(fields)),
        InstKind::GetField { object, field } => format!("field {}.{field}", name(*object)),
        InstKind::SetField {
            object,
            field,
            value,
        } => format!("set {}.{field} = {}", name(*object), name(*value)),
        InstKind::MakeEnum {
            ty,
            variant,
            payload,
        } => format!("enum {ty}#{variant}({})", list(payload)),
        InstKind::GetTag { value } => format!("tag {}", name(*value)),
        InstKind::GetPayload {
            value,
            variant,
            field,
        } => format!("payload {}#{variant}.{field}", name(*value)),
        InstKind::MakeTuple(values) => format!("tuple ({})", list(values)),
        InstKind::GetElement { tuple, index } => format!("element {}.{index}", name(*tuple)),
        InstKind::MakeList { element, values } => {
            format!("list<{element}> [{}]", list(values))
        }
        InstKind::MakeMap {
            key,
            value,
            entries,
        } => {
            let pairs: Vec<String> = entries
                .iter()
                .map(|(k, v)| format!("{} = {}", name(*k), name(*v)))
                .collect();
            format!("map<{key}, {value}> {{ {} }}", pairs.join(", "))
        }
        InstKind::MakeSet { element, values } => {
            format!("set<{element}> {{ {} }}", list(values))
        }
        InstKind::GetIndex { receiver, index } => {
            format!("index {}[{}]", name(*receiver), name(*index))
        }
        InstKind::SetIndex {
            receiver,
            index,
            value,
        } => format!(
            "set {}[{}] = {}",
            name(*receiver),
            name(*index),
            name(*value)
        ),
        InstKind::MakeSome { value } => format!("some {}", name(*value)),
        InstKind::IsSome { value } => format!("is some {}", name(*value)),
        InstKind::Unwrap { value } => format!("unwrap {}", name(*value)),
        InstKind::AddressOf { mutable, slot } => {
            let qualifier = if *mutable { "mut " } else { "" };
            format!("address {qualifier}slot{}", slot.0)
        }
        InstKind::Load { pointer } => format!("load {}", name(*pointer)),
        InstKind::Store { pointer, value } => {
            format!("store {} = {}", name(*pointer), name(*value))
        }
        InstKind::SlotGet { slot } => format!("get slot{}", slot.0),
        InstKind::SlotSet { slot, value } => format!("set slot{} = {}", slot.0, name(*value)),
    };

    match inst.result {
        Some(result) => format!("{}: {} = {body}", name(result), function.type_of(result)),
        None => body,
    }
}

fn constant(value: &Const) -> String {
    match value {
        Const::Unit => "()".to_owned(),
        Const::Nil => "nil".to_owned(),
        Const::Bool(value) => value.to_string(),
        Const::Int(value) => value.to_string(),
        Const::Float(value) => format!("{value:?}"),
        Const::Char(value) => format!("{value:?}"),
        Const::Str(value) => format!("{value:?}"),
        Const::Bytes(value) => format!("{value:?}"),
    }
}

fn target(target: &Target) -> String {
    if target.args.is_empty() {
        format!("block{}", target.block.0)
    } else {
        format!("block{}({})", target.block.0, list(&target.args))
    }
}

fn terminator(term: &Terminator) -> String {
    match term {
        Terminator::Jump(to) => format!("jump {}", target(to)),
        Terminator::Branch {
            condition,
            then,
            otherwise,
        } => format!(
            "branch {} {} else {}",
            name(*condition),
            target(then),
            target(otherwise)
        ),
        Terminator::Switch {
            value,
            cases,
            default,
        } => {
            let arms: Vec<String> = cases
                .iter()
                .map(|(tag, to)| format!("{tag} => {}", target(to)))
                .collect();
            format!(
                "switch {} [{}] else {}",
                name(*value),
                arms.join(", "),
                target(default)
            )
        }
        Terminator::Return(value) => format!("return {}", name(*value)),
        Terminator::Trap(trap) => format!("trap {}", trap.spelling()),
    }
}

fn unary(op: UnaryOp) -> &'static str {
    match op {
        UnaryOp::Negate => "neg",
        UnaryOp::Not => "not",
        UnaryOp::BitNot => "bitnot",
    }
}

fn binary(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Add => "add",
        BinaryOp::Subtract => "sub",
        BinaryOp::Multiply => "mul",
        BinaryOp::Divide => "div",
        BinaryOp::IntegerDivide => "idiv",
        BinaryOp::Remainder => "rem",
        BinaryOp::Power => "pow",
        BinaryOp::Concat => "concat",
        BinaryOp::Equal => "eq",
        BinaryOp::NotEqual => "ne",
        BinaryOp::Less => "lt",
        BinaryOp::LessEqual => "le",
        BinaryOp::Greater => "gt",
        BinaryOp::GreaterEqual => "ge",
        BinaryOp::BitAnd => "and",
        BinaryOp::BitOr => "or",
        BinaryOp::BitXor => "xor",
        BinaryOp::ShiftLeft => "shl",
        BinaryOp::ShiftRight => "shr",
    }
}
