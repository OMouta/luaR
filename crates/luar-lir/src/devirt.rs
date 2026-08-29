//! Devirtualization of single-implementation interface calls (LR18.1).

use std::collections::{HashMap, HashSet};

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
    erase_unused_tables(program, &single);
}

fn erase_unused_tables(program: &mut Program, single: &HashMap<TypeId, Implementation>) {
    let unresolved: HashSet<TypeId> = program
        .functions()
        .flat_map(|(_, function)| function.blocks())
        .flat_map(|(_, block)| &block.insts)
        .filter_map(|inst| match inst.kind {
            InstKind::CallVirtual { method, .. } => Some(method.interface),
            _ => None,
        })
        .collect();

    let functions: Vec<FuncId> = program.functions().map(|(id, _)| id).collect();
    for id in functions {
        let function = program.function_mut(id);
        for block in function.blocks_mut() {
            for inst in &mut block.insts {
                let InstKind::MakeDyn { interface, .. } = &mut inst.kind else {
                    continue;
                };
                if interface.is_some_and(|id| single.contains_key(&id) && !unresolved.contains(&id))
                {
                    *interface = None;
                }
            }
        }
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
        let found: Vec<(usize, FuncId, Vec<Ty>, Ty)> = program
            .function(id)
            .block(block)
            .insts
            .iter()
            .enumerate()
            .filter_map(|(at, inst)| match &inst.kind {
                InstKind::CallVirtual {
                    method, receiver, ..
                } => {
                    let held = single.get(&method.interface)?;
                    let callee = *held.methods.get(method.slot as usize)?;
                    let (type_args, receiver) =
                        type_arguments(program, id, *method, *receiver, callee)?;
                    Some((at, callee, type_args, receiver))
                }
                _ => None,
            })
            .collect();

        if found.is_empty() {
            continue;
        }

        // The implementation takes its own type as the receiver, so the
        // interface value has to be opened before it is passed.
        let opened: Vec<_> = found
            .iter()
            .map(|(_, _, _, receiver)| receiver.clone())
            .map(|ty| program.function_mut(id).add_value(ty))
            .collect();

        let insts = program.function(id).block(block).insts.clone();
        let mut built = Vec::with_capacity(insts.len() + found.len());

        for (at, inst) in insts.into_iter().enumerate() {
            let Some(index) = found.iter().position(|(held, _, _, _)| *held == at) else {
                built.push(inst);
                continue;
            };

            let (_, callee, type_args, _) = &found[index];
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
                    callee: *callee,
                    type_args: type_args.clone(),
                    args: passed,
                },
                span: inst.span,
            });
        }

        program.function_mut(id).block_mut(block).insts = built;
    }
}

fn type_arguments(
    program: &Program,
    caller: FuncId,
    method: crate::inst::MethodId,
    receiver: crate::inst::Value,
    callee: FuncId,
) -> Option<(Vec<Ty>, Ty)> {
    let Ty::Named {
        id,
        args: interface_args,
    } = program.function(caller).type_of(receiver)
    else {
        return None;
    };
    if *id != method.interface {
        return None;
    }

    let nominal = program.nominal(method.interface);
    let Shape::Interface(interface) = &nominal.shape else {
        return None;
    };
    let required = interface.methods.get(method.slot as usize)?;
    let params: Vec<Ty> = required
        .params
        .iter()
        .map(|ty| ty.substitute(&nominal.type_params, interface_args))
        .collect();
    let result = required
        .result
        .substitute(&nominal.type_params, interface_args);

    let function = program.function(callee);
    if function.params.len() != params.len() + 1 {
        return None;
    }
    let mut inferred = vec![None; function.type_params.len()];
    for (pattern, concrete) in function.params.iter().skip(1).zip(&params) {
        infer(&function.type_params, pattern, concrete, &mut inferred)?;
    }
    infer(
        &function.type_params,
        &function.result,
        &result,
        &mut inferred,
    )?;
    let type_args: Vec<Ty> = inferred.into_iter().collect::<Option<_>>()?;
    let receiver = function
        .params
        .first()?
        .substitute(&function.type_params, &type_args);
    Some((type_args, receiver))
}

fn infer(
    params: &[String],
    pattern: &Ty,
    concrete: &Ty,
    inferred: &mut [Option<Ty>],
) -> Option<()> {
    if let Ty::Parameter(name) = pattern {
        let Some(index) = params.iter().position(|param| param == name) else {
            return (pattern == concrete).then_some(());
        };
        return match &inferred[index] {
            Some(held) => (held == concrete).then_some(()),
            None => {
                inferred[index] = Some(concrete.clone());
                Some(())
            }
        };
    }

    match (pattern, concrete) {
        (Ty::Named { id: left, args: a }, Ty::Named { id: right, args: b }) if left == right => {
            infer_each(params, a, b, inferred)
        }
        (
            Ty::Builtin {
                kind: left,
                args: a,
            },
            Ty::Builtin {
                kind: right,
                args: b,
            },
        ) if left == right => infer_each(params, a, b, inferred),
        (Ty::Tuple(a), Ty::Tuple(b)) | (Ty::Union(a), Ty::Union(b)) => {
            infer_each(params, a, b, inferred)
        }
        (Ty::Record(a), Ty::Record(b)) if a.len() == b.len() => {
            for ((left_name, left), (right_name, right)) in a.iter().zip(b) {
                if left_name != right_name {
                    return None;
                }
                infer(params, left, right, inferred)?;
            }
            Some(())
        }
        (Ty::Optional(a), Ty::Optional(b)) | (Ty::Array(a), Ty::Array(b)) => {
            infer(params, a, b, inferred)
        }
        (
            Ty::Pointer {
                mutable: left_mutable,
                target: left,
            },
            Ty::Pointer {
                mutable: right_mutable,
                target: right,
            },
        ) if left_mutable == right_mutable => infer(params, left, right, inferred),
        (
            Ty::Function {
                params: left_params,
                result: left_result,
            },
            Ty::Function {
                params: right_params,
                result: right_result,
            },
        ) => {
            infer_each(params, left_params, right_params, inferred)?;
            infer(params, left_result, right_result, inferred)
        }
        _ => (pattern == concrete).then_some(()),
    }
}

fn infer_each(
    params: &[String],
    patterns: &[Ty],
    concrete: &[Ty],
    inferred: &mut [Option<Ty>],
) -> Option<()> {
    if patterns.len() != concrete.len() {
        return None;
    }
    for (pattern, concrete) in patterns.iter().zip(concrete) {
        infer(params, pattern, concrete, inferred)?;
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inst::{Const, MethodId, Terminator};
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
                    repr_c: false,
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

    #[test]
    fn a_resolved_interface_value_needs_no_method_table() {
        let (mut program, _, interface) = program_with(1);
        let Shape::Interface(held) = &program.nominal(interface).shape else {
            unreachable!()
        };
        let concrete = Ty::Named {
            id: held.implementors[0].ty,
            args: Vec::new(),
        };
        let mut caller = Function::new("box".to_owned(), Vec::new(), Ty::Unit, SPAN);
        let value = caller.add_value(concrete.clone());
        caller.block_mut(caller.entry).insts.push(Inst {
            result: Some(value),
            kind: InstKind::MakeStruct {
                ty: concrete,
                fields: Vec::new(),
            },
            span: SPAN,
        });
        let boxed = caller.add_value(Ty::Named {
            id: interface,
            args: Vec::new(),
        });
        caller.block_mut(caller.entry).insts.push(Inst {
            result: Some(boxed),
            kind: InstKind::MakeDyn {
                interface: Some(interface),
                value,
            },
            span: SPAN,
        });
        let unit = caller.add_value(Ty::Unit);
        caller.block_mut(caller.entry).insts.push(Inst {
            result: Some(unit),
            kind: InstKind::Const(Const::Unit),
            span: SPAN,
        });
        caller.block_mut(caller.entry).term = Some(Terminator::Return(unit));
        let caller = program.add_function(caller);

        run(&mut program);

        let interface = program
            .function(caller)
            .block(program.function(caller).entry)
            .insts
            .iter()
            .find_map(|inst| match inst.kind {
                InstKind::MakeDyn { interface, .. } => Some(interface),
                _ => None,
            });
        assert_eq!(interface, Some(None));
    }

    #[test]
    fn a_generic_implementation_is_instantiated() {
        let mut program = Program::default();
        let interface = program.add_type(Nominal {
            name: "Source".to_owned(),
            type_params: vec!["T".to_owned()],
            shape: Shape::Interface(Interface {
                methods: vec![Method {
                    name: "take".to_owned(),
                    params: Vec::new(),
                    result: Ty::Parameter("T".to_owned()),
                }],
                implementors: Vec::new(),
            }),
            span: SPAN,
        });
        let holder = program.add_type(Nominal {
            name: "Holder".to_owned(),
            type_params: vec!["U".to_owned()],
            shape: Shape::Struct(Struct {
                fields: Vec::new(),
                reference: false,
                repr_c: false,
            }),
            span: SPAN,
        });
        let generic_holder = Ty::Named {
            id: holder,
            args: vec![Ty::Parameter("U".to_owned())],
        };
        let mut take = Function::new(
            "Holder.take".to_owned(),
            vec![generic_holder],
            Ty::Parameter("U".to_owned()),
            SPAN,
        );
        take.type_params = vec!["U".to_owned()];
        let returned = take.block(take.entry).params[0];
        take.block_mut(take.entry).term = Some(Terminator::Return(returned));
        let take = program.add_function(take);
        let Shape::Interface(held) = &mut program.nominal_mut(interface).shape else {
            unreachable!()
        };
        held.implementors.push(Implementation {
            ty: holder,
            methods: vec![take],
        });

        let seen = Ty::Named {
            id: interface,
            args: vec![Ty::INT],
        };
        let mut caller = Function::new("read".to_owned(), vec![seen], Ty::INT, SPAN);
        let receiver = caller.block(caller.entry).params[0];
        let result = caller.add_value(Ty::INT);
        caller.block_mut(caller.entry).insts.push(Inst {
            result: Some(result),
            kind: InstKind::CallVirtual {
                method: MethodId { interface, slot: 0 },
                receiver,
                args: Vec::new(),
            },
            span: SPAN,
        });
        caller.block_mut(caller.entry).term = Some(Terminator::Return(result));
        let caller = program.add_function(caller);

        run(&mut program);
        crate::mono::run(&mut program);

        let reached = program
            .function(caller)
            .block(program.function(caller).entry)
            .insts
            .iter()
            .find_map(|inst| match inst.kind {
                InstKind::Call { callee, .. } => Some(callee),
                _ => None,
            })
            .expect("a direct call");
        assert!(!program.function(reached).is_template());
        assert_eq!(
            program.function(reached).params,
            [Ty::Named {
                id: holder,
                args: vec![Ty::INT]
            }]
        );
    }
}
