//! The implementations a primitive has of the prelude's protocols (LR35).

use luar_diagnostics::Span;

use crate::inst::{BinaryOp, Const, Inst, InstKind, Target, Terminator, Value};
use crate::program::{BlockId, Function, Implementation, Program, Shape};
use crate::ty::{IntTy, Ty, TypeId};

/// The implementation `held` has of `interface`, written the first time
/// something asks for it. `None` where `held` does not satisfy the protocol
/// without declaring it.
pub fn implementation(
    program: &mut Program,
    interface: TypeId,
    held: &Ty,
) -> Option<Implementation> {
    let nominal = program.nominal(interface);
    let Shape::Interface(shape) = &nominal.shape else {
        return None;
    };
    if let Some(found) = shape
        .implementors
        .iter()
        .find(|candidate| candidate.covers(held))
    {
        return Some(found.clone());
    }
    let protocol = nominal.name.strip_prefix("std/prelude.")?.to_owned();
    let span = nominal.span;
    let names: Vec<String> = shape
        .methods
        .iter()
        .map(|method| method.name.clone())
        .collect();

    let written: Option<Vec<Function>> = names
        .iter()
        .map(|name| method(&protocol, name, held, span))
        .collect();
    let methods = written?
        .into_iter()
        .map(|function| program.add_function(function))
        .collect();
    let built = Implementation {
        ty: held.clone(),
        methods,
    };
    if let Shape::Interface(shape) = &mut program.nominal_mut(interface).shape {
        shape.implementors.push(built.clone());
    }
    Some(built)
}

fn method(protocol: &str, name: &str, held: &Ty, span: Span) -> Option<Function> {
    match (protocol, name) {
        ("Display", "display") => display(held, span),
        ("Eq", "eq") => eq(held, span),
        ("Hash", "hash") => hash(held, span),
        ("Comparable", "compare") => compare(held, span),
        _ => None,
    }
}

/// LR35: the literal form of a primitive.
fn display(held: &Ty, span: Span) -> Option<Function> {
    let mut function = Function::new(format!("{held}.display"), vec![held.clone()], Ty::Str, span);
    let entry = function.entry;
    let value = function.block(entry).params[0];
    let text = match held {
        Ty::Str => value,
        Ty::Int(_) | Ty::Float(_) | Ty::Char => emit(
            &mut function,
            entry,
            InstKind::DisplayValue { value },
            Ty::Str,
            span,
        ),
        Ty::Nil => text(&mut function, entry, "nil", span),
        Ty::Bool => {
            let yes = function.add_block();
            let no = function.add_block();
            let join = function.add_block();
            function.block_mut(entry).term = Some(Terminator::Branch {
                condition: value,
                then: Target::to(yes),
                otherwise: Target::to(no),
            });
            for (block, spelled) in [(yes, "true"), (no, "false")] {
                let text = text(&mut function, block, spelled, span);
                function.block_mut(block).term =
                    Some(Terminator::Jump(Target::new(join, vec![text])));
            }
            let joined = function.add_block_param(join, Ty::Str);
            function.block_mut(join).term = Some(Terminator::Return(joined));
            return Some(function);
        }
        _ => return None,
    };
    function.block_mut(entry).term = Some(Terminator::Return(text));
    Some(function)
}

/// LR11.3: the built-in comparison.
fn eq(held: &Ty, span: Span) -> Option<Function> {
    let mut function = Function::new(
        format!("{held}.eq"),
        vec![held.clone(), held.clone()],
        Ty::Bool,
        span,
    );
    let entry = function.entry;
    let [left, right] = function.block(entry).params[..] else {
        return None;
    };
    let equal = match held {
        Ty::Unit | Ty::Nil => emit(
            &mut function,
            entry,
            InstKind::Const(Const::Bool(true)),
            Ty::Bool,
            span,
        ),
        Ty::Bool | Ty::Int(_) | Ty::Float(_) | Ty::Char | Ty::Str | Ty::Bytes => emit(
            &mut function,
            entry,
            InstKind::Binary {
                op: BinaryOp::Equal,
                left,
                right,
            },
            Ty::Bool,
            span,
        ),
        _ => return None,
    };
    function.block_mut(entry).term = Some(Terminator::Return(equal));
    Some(function)
}

fn hash(held: &Ty, span: Span) -> Option<Function> {
    if !matches!(
        held,
        Ty::Unit | Ty::Nil | Ty::Bool | Ty::Int(_) | Ty::Float(_) | Ty::Char | Ty::Str | Ty::Bytes
    ) {
        return None;
    }
    let mut function = Function::new(
        format!("{held}.hash"),
        vec![held.clone()],
        Ty::Int(IntTy::U64),
        span,
    );
    let entry = function.entry;
    let value = function.block(entry).params[0];
    let hashed = emit(
        &mut function,
        entry,
        InstKind::HashValue { value },
        Ty::Int(IntTy::U64),
        span,
    );
    function.block_mut(entry).term = Some(Terminator::Return(hashed));
    Some(function)
}

/// Negative, zero, or positive as the receiver orders before, with, or after
/// the argument (LR11.3).
fn compare(held: &Ty, span: Span) -> Option<Function> {
    if !matches!(held, Ty::Int(_) | Ty::Float(_) | Ty::Char | Ty::Str) {
        return None;
    }
    let mut function = Function::new(
        format!("{held}.compare"),
        vec![held.clone(), held.clone()],
        Ty::INT,
        span,
    );
    let entry = function.entry;
    let [left, right] = function.block(entry).params[..] else {
        return None;
    };
    let before = function.add_block();
    let not_before = function.add_block();
    let after = function.add_block();
    let same = function.add_block();

    let less = ordered(&mut function, entry, BinaryOp::Less, left, right, span);
    function.block_mut(entry).term = Some(Terminator::Branch {
        condition: less,
        then: Target::to(before),
        otherwise: Target::to(not_before),
    });
    let greater = ordered(
        &mut function,
        not_before,
        BinaryOp::Greater,
        left,
        right,
        span,
    );
    function.block_mut(not_before).term = Some(Terminator::Branch {
        condition: greater,
        then: Target::to(after),
        otherwise: Target::to(same),
    });
    for (block, ordering) in [(before, -1i64), (after, 1), (same, 0)] {
        let answer = emit(
            &mut function,
            block,
            InstKind::Const(Const::Int(ordering as u64)),
            Ty::INT,
            span,
        );
        function.block_mut(block).term = Some(Terminator::Return(answer));
    }
    Some(function)
}

fn ordered(
    function: &mut Function,
    block: BlockId,
    op: BinaryOp,
    left: Value,
    right: Value,
    span: Span,
) -> Value {
    emit(
        function,
        block,
        InstKind::Binary { op, left, right },
        Ty::Bool,
        span,
    )
}

fn text(function: &mut Function, block: BlockId, spelled: &str, span: Span) -> Value {
    emit(
        function,
        block,
        InstKind::Const(Const::Str(spelled.to_owned())),
        Ty::Str,
        span,
    )
}

fn emit(function: &mut Function, block: BlockId, kind: InstKind, ty: Ty, span: Span) -> Value {
    let value = function.add_value(ty);
    function.block_mut(block).insts.push(Inst {
        result: Some(value),
        kind,
        span,
    });
    value
}
