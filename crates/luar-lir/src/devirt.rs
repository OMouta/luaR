//! Devirtualization of single-implementation interface calls (LR18.1).
//!
//! A call through an interface dispatches at runtime because the value could
//! be any implementation. Where the whole program has exactly one, it cannot:
//! there is one function it can reach, and the call may name it directly.
//!
//! LR18.1 requires the semantics to preserve dynamic dispatch, and this does.
//! Nothing about which function runs changes; what changes is whether the
//! program looks it up to find that out.
//!
//! This is a whole-program question, like monomorphization: a second
//! implementation in another module is what makes the answer no.

use std::collections::HashMap;

use crate::inst::{Inst, InstKind};
use crate::program::{FuncId, Implementation, Program, Shape};
use crate::ty::{Ty, TypeId};

/// Replaces every call through an interface that has one implementation with
/// a direct call to it.
pub fn run(program: &mut Program) {
    let single = single_implementations(program);
    if single.is_empty() {
        return;
    }

    let functions: Vec<FuncId> = program.functions().map(|(id, _)| id).collect();
    for id in functions {
        devirtualize(program, id, &single);
    }
}

/// The interfaces exactly one type implements, and that implementation.
fn single_implementations(program: &Program) -> HashMap<TypeId, Implementation> {
    program
        .types()
        .filter_map(|(id, nominal)| match &nominal.shape {
            Shape::Interface(interface) => match interface.implementors.as_slice() {
                [only] => Some((id, only.clone())),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

fn devirtualize(program: &mut Program, id: FuncId, single: &HashMap<TypeId, Implementation>) {
    let blocks: Vec<crate::program::BlockId> = program
        .function(id)
        .blocks()
        .map(|(block, _)| block)
        .collect();

    for block in blocks {
        // Which calls in this block can be resolved, and to what.
        let found: Vec<(usize, FuncId)> = program
            .function(id)
            .block(block)
            .insts
            .iter()
            .enumerate()
            .filter_map(|(at, inst)| match &inst.kind {
                InstKind::CallVirtual { method, .. } => {
                    let held = single.get(&method.interface)?;
                    Some((at, *held.methods.get(method.slot as usize)?))
                }
                _ => None,
            })
            .collect();

        if found.is_empty() {
            continue;
        }

        // The implementation takes its own type as the receiver, so the
        // interface value has to be opened before it is passed.
        let receivers: Vec<Ty> = found
            .iter()
            .map(|(_, callee)| {
                program
                    .function(*callee)
                    .params
                    .first()
                    .cloned()
                    .unwrap_or(Ty::Never)
            })
            .collect();
        let opened: Vec<_> = receivers
            .into_iter()
            .map(|ty| program.function_mut(id).add_value(ty))
            .collect();

        let insts = program.function(id).block(block).insts.clone();
        let mut built = Vec::with_capacity(insts.len() + found.len());

        for (at, inst) in insts.into_iter().enumerate() {
            let Some(index) = found.iter().position(|(held, _)| *held == at) else {
                built.push(inst);
                continue;
            };

            let (_, callee) = found[index];
            let inside = opened[index];
            let InstKind::CallVirtual { receiver, args, .. } = inst.kind else {
                unreachable!("only a virtual call was found here")
            };

            built.push(Inst {
                result: Some(inside),
                kind: InstKind::DynValue { value: receiver },
                span: inst.span,
            });

            let mut passed = Vec::with_capacity(args.len() + 1);
            passed.push(inside);
            passed.extend(args);
            built.push(Inst {
                result: inst.result,
                kind: InstKind::Call {
                    callee,
                    type_args: Vec::new(),
                    args: passed,
                },
                span: inst.span,
            });
        }

        program.function_mut(id).block_mut(block).insts = built;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inst::{MethodId, Terminator};
    use crate::program::{Function, Interface, Method, Nominal, Shape, Struct};
    use luar_diagnostics::{FileId, Span};

    const SPAN: Span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };

    /// An interface with one method, `count` types implementing it, and a
    /// function calling it through the interface.
    fn program_with(count: usize) -> (Program, FuncId, TypeId) {
        let mut program = Program::default();

        let interface = program.add_type(Nominal {
            name: "Sized".to_owned(),
            type_params: Vec::new(),
            shape: Shape::Interface(Interface {
                methods: vec![Method {
                    name: "size".to_owned(),
                    params: Vec::new(),
                    result: Ty::INT,
                }],
                implementors: Vec::new(),
            }),
            span: SPAN,
        });

        let mut implementors = Vec::new();
        for which in 0..count {
            let ty = program.add_type(Nominal {
                name: format!("Small{which}"),
                type_params: Vec::new(),
                shape: Shape::Struct(Struct {
                    fields: Vec::new(),
                    reference: false,
                }),
                span: SPAN,
            });
            let receiver = Ty::Named {
                id: ty,
                args: Vec::new(),
            };
            let mut size =
                Function::new(format!("Small{which}.size"), vec![receiver], Ty::INT, SPAN);
            let held = size.block(size.entry).params[0];
            size.block_mut(size.entry).term = Some(Terminator::Return(held));
            let size = program.add_function(size);
            implementors.push(Implementation {
                ty,
                methods: vec![size],
            });
        }

        if let Shape::Interface(held) = &mut program.nominal_mut(interface).shape {
            held.implementors = implementors;
        }

        let seen = Ty::Named {
            id: interface,
            args: Vec::new(),
        };
        let mut caller = Function::new("measure".to_owned(), vec![seen], Ty::INT, SPAN);
        let entry = caller.entry;
        let receiver = caller.block(entry).params[0];
        let result = caller.add_value(Ty::INT);
        caller.block_mut(entry).insts.push(Inst {
            result: Some(result),
            kind: InstKind::CallVirtual {
                method: MethodId { interface, slot: 0 },
                receiver,
                args: Vec::new(),
            },
            span: SPAN,
        });
        caller.block_mut(entry).term = Some(Terminator::Return(result));
        let measure = program.add_function(caller);

        (program, measure, interface)
    }

    fn kinds(program: &Program, id: FuncId) -> Vec<&'static str> {
        program
            .function(id)
            .blocks()
            .flat_map(|(_, block)| block.insts.iter())
            .map(|inst| match &inst.kind {
                InstKind::CallVirtual { .. } => "virtual",
                InstKind::Call { .. } => "direct",
                InstKind::DynValue { .. } => "open",
                _ => "other",
            })
            .collect()
    }

    #[test]
    fn one_implementation_makes_the_call_direct() {
        let (mut program, measure, _) = program_with(1);
        run(&mut program);
        assert_eq!(kinds(&program, measure), ["open", "direct"]);
    }

    #[test]
    fn the_direct_call_reaches_the_one_implementation() {
        let (mut program, measure, interface) = program_with(1);
        let Shape::Interface(held) = &program.nominal(interface).shape else {
            panic!("an interface");
        };
        let only = held.implementors[0].methods[0];

        run(&mut program);

        let reached = program
            .function(measure)
            .blocks()
            .flat_map(|(_, block)| block.insts.iter())
            .find_map(|inst| match &inst.kind {
                InstKind::Call { callee, .. } => Some(*callee),
                _ => None,
            });
        assert_eq!(reached, Some(only));
    }

    #[test]
    fn two_implementations_leave_the_call_dispatching() {
        let (mut program, measure, _) = program_with(2);
        run(&mut program);
        assert_eq!(kinds(&program, measure), ["virtual"]);
    }

    #[test]
    fn an_interface_nothing_implements_leaves_the_call_alone() {
        let (mut program, measure, _) = program_with(0);
        run(&mut program);
        assert_eq!(kinds(&program, measure), ["virtual"]);
    }
}
