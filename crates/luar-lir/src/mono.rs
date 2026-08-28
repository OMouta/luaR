//! Whole-program monomorphization (LR19).

use std::collections::HashMap;

use crate::inst::InstKind;
use crate::program::{FuncId, Function, Program};
use crate::ty::Ty;

/// Replaces every call to a generic function with a call to an instance of it.
pub fn run(program: &mut Program) {
    let mut mono = Mono {
        made: HashMap::new(),
        pending: Vec::new(),
    };

    // Every function that is not a template is code the program keeps, so each
    // one is a place a call can be waiting.
    let roots: Vec<FuncId> = program
        .functions()
        .filter(|(_, function)| !function.is_template())
        .map(|(id, _)| id)
        .collect();

    for id in roots {
        mono.rewrite(program, id);
    }

    // Each instance is itself code, and the calls inside it are the next
    // round.
    while let Some(id) = mono.pending.pop() {
        mono.rewrite(program, id);
    }

    mono.finalizers(program);
}

/// One instance: the template, and what filled its parameters.
type Instance = (FuncId, Vec<Ty>);

struct Mono {
    made: HashMap<Instance, FuncId>,
    pending: Vec<FuncId>,
}

impl Mono {
    /// Points every generic call in `id` at an instance, making the instance
    /// where this is the first call to ask for it.
    fn rewrite(&mut self, program: &mut Program, id: FuncId) {
        let calls: Vec<(usize, usize, FuncId, Vec<Ty>)> = program
            .function(id)
            .blocks()
            .flat_map(|(block, held)| {
                held.insts
                    .iter()
                    .enumerate()
                    .filter_map(move |(at, inst)| match &inst.kind {
                        InstKind::Call {
                            callee, type_args, ..
                        } if !type_args.is_empty() => {
                            Some((block.0 as usize, at, *callee, type_args.clone()))
                        }
                        _ => None,
                    })
            })
            .collect();

        for (block, at, callee, args) in calls {
            let instance = self.instance(program, callee, args);
            let block =
                crate::program::BlockId(u32::try_from(block).expect("block count fits in u32"));
            let inst = &mut program.function_mut(id).block_mut(block).insts[at];
            if let InstKind::Call {
                callee, type_args, ..
            } = &mut inst.kind
            {
                *callee = instance;
                type_args.clear();
            }
        }
    }

    /// The instance of `template` for `args`, made if nothing has asked for
    /// it before.
    fn instance(&mut self, program: &mut Program, template: FuncId, args: Vec<Ty>) -> FuncId {
        if let Some(made) = self.made.get(&(template, args.clone())) {
            return *made;
        }

        let built = substituted(program.function(template), &args);
        let id = program.add_function(built);
        self.made.insert((template, args), id);
        self.pending.push(id);
        id
    }

    fn finalizers(&mut self, program: &mut Program) {
        let templates: Vec<(Ty, FuncId)> = program
            .finalizers()
            .map(|(ty, function)| (ty.clone(), function))
            .collect();
        let mut finalizers = HashMap::new();

        loop {
            while let Some(id) = self.pending.pop() {
                self.rewrite(program, id);
            }

            let mut receivers = Vec::new();
            for (_, function) in program
                .functions()
                .filter(|(_, function)| !function.is_template())
            {
                for (_, ty) in function.values() {
                    if matches!(ty, Ty::Named { .. }) && concrete(ty) && !receivers.contains(ty) {
                        receivers.push(ty.clone());
                    }
                }
            }

            let mut added = false;
            for receiver in receivers {
                if finalizers.contains_key(&receiver) {
                    continue;
                }
                let Ty::Named { id, args } = &receiver else {
                    continue;
                };
                let Some((_, template)) = templates.iter().find(
                    |(ty, _)| matches!(ty, Ty::Named { id: candidate, .. } if candidate == id),
                ) else {
                    continue;
                };
                let function = if program.function(*template).is_template() {
                    self.instance(program, *template, args.clone())
                } else {
                    *template
                };
                finalizers.insert(receiver, function);
                added = true;
            }

            if !added {
                break;
            }
        }

        program.replace_finalizers(finalizers);
    }
}

fn concrete(ty: &Ty) -> bool {
    match ty {
        Ty::Parameter(_) => false,
        Ty::Named { args, .. } | Ty::Builtin { args, .. } | Ty::Tuple(args) | Ty::Union(args) => {
            args.iter().all(concrete)
        }
        Ty::Record(fields) => fields.iter().all(|(_, ty)| concrete(ty)),
        Ty::Optional(held) | Ty::Array(held) => concrete(held),
        Ty::Pointer { target, .. } => concrete(target),
        Ty::Function { params, result } => params.iter().all(concrete) && concrete(result),
        _ => true,
    }
}

/// A copy of `template` with `args` where its type parameters were.
fn substituted(template: &Function, args: &[Ty]) -> Function {
    let params = template.type_params.clone();
    let fill = |ty: &Ty| ty.substitute(&params, args);

    let mut built = template.clone();
    built.name = format!("{}<{}>", template.name, spelling(args));
    built.type_params.clear();
    built.params = template.params.iter().map(&fill).collect();
    built.result = fill(&template.result);
    substitute_types(&mut built, &params, args);
    built
}

fn spelling(args: &[Ty]) -> String {
    args.iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

/// Replaces `params` with `args` in every type `function` mentions: the type
/// of each value and slot, and the types written into the instructions.
fn substitute_types(function: &mut Function, params: &[String], args: &[Ty]) {
    function.substitute_values(params, args);

    for block in function.blocks_mut() {
        for inst in &mut block.insts {
            match &mut inst.kind {
                InstKind::Convert { to, .. } => *to = to.substitute(params, args),
                InstKind::IsType { ty, .. } | InstKind::MakeStruct { ty, .. } => {
                    *ty = ty.substitute(params, args);
                }
                InstKind::MakeEnum { ty, .. } => *ty = ty.substitute(params, args),
                InstKind::MakeList { element, .. } | InstKind::MakeSet { element, .. } => {
                    *element = element.substitute(params, args);
                }
                InstKind::MakeMap { key, value, .. } => {
                    *key = key.substitute(params, args);
                    *value = value.substitute(params, args);
                }
                // A call inside a template carries the template's own
                // parameters in its arguments, so those are filled in too and
                // the call becomes one this pass can instantiate.
                InstKind::Call { type_args, .. } => {
                    for arg in type_args.iter_mut() {
                        *arg = arg.substitute(params, args);
                    }
                }
                _ => {}
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inst::{Const, Inst, Terminator};
    use luar_diagnostics::{FileId, Span};

    const SPAN: Span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };

    /// A template `identity<T>(T) -> T`, and a caller of it.
    fn program_with_two_calls() -> (Program, FuncId) {
        let mut program = Program::default();

        let mut template = Function::new(
            "identity".to_owned(),
            vec![Ty::Parameter("T".to_owned())],
            Ty::Parameter("T".to_owned()),
            SPAN,
        );
        template.type_params = vec!["T".to_owned()];
        let held = template.block(template.entry).params[0];
        template.block_mut(template.entry).term = Some(Terminator::Return(held));
        let identity = program.add_function(template);

        let mut caller = Function::new("main".to_owned(), Vec::new(), Ty::INT, SPAN);
        let entry = caller.entry;
        let mut last = None;
        for (ty, args) in [
            (Ty::INT, vec![Ty::INT]),
            (Ty::Str, vec![Ty::Str]),
            (Ty::INT, vec![Ty::INT]),
        ] {
            let argument = caller.add_value(ty.clone());
            caller.block_mut(entry).insts.push(Inst {
                result: Some(argument),
                kind: InstKind::Const(Const::Int(1)),
                span: SPAN,
            });
            let result = caller.add_value(ty);
            caller.block_mut(entry).insts.push(Inst {
                result: Some(result),
                kind: InstKind::Call {
                    callee: identity,
                    type_args: args,
                    args: vec![argument],
                },
                span: SPAN,
            });
            last = Some(result);
        }
        caller.block_mut(entry).term = Some(Terminator::Return(last.expect("three calls")));
        let main = program.add_function(caller);

        (program, main)
    }

    #[test]
    fn one_instance_per_set_of_type_arguments() {
        let (mut program, main) = program_with_two_calls();
        run(&mut program);

        let reached: Vec<FuncId> = program
            .function(main)
            .blocks()
            .flat_map(|(_, block)| block.insts.iter())
            .filter_map(|inst| match &inst.kind {
                InstKind::Call { callee, .. } => Some(*callee),
                _ => None,
            })
            .collect();

        // Two calls asked for `int` and one for `string`, so there are two
        // instances and the two `int` calls share one.
        assert_eq!(reached[0], reached[2]);
        assert_ne!(reached[0], reached[1]);
        assert_eq!(program.functions().count(), 4);
    }

    #[test]
    fn an_instance_has_its_parameters_filled_in() {
        let (mut program, main) = program_with_two_calls();
        run(&mut program);

        let first = program
            .function(main)
            .blocks()
            .flat_map(|(_, block)| block.insts.iter())
            .find_map(|inst| match &inst.kind {
                InstKind::Call { callee, .. } => Some(*callee),
                _ => None,
            })
            .expect("a call");

        let instance = program.function(first);
        assert!(!instance.is_template());
        assert_eq!(instance.params, [Ty::INT]);
        assert_eq!(instance.result, Ty::INT);
        assert_eq!(
            instance.type_of(instance.block(instance.entry).params[0]),
            &Ty::INT
        );
    }

    #[test]
    fn no_call_carries_type_arguments_afterwards() {
        let (mut program, _) = program_with_two_calls();
        run(&mut program);

        let carried = program
            .functions()
            .filter(|(_, function)| !function.is_template())
            .flat_map(|(_, function)| {
                function
                    .blocks()
                    .flat_map(|(_, block)| block.insts.iter())
                    .filter_map(|inst| match &inst.kind {
                        InstKind::Call { type_args, .. } => Some(type_args.len()),
                        _ => None,
                    })
                    .collect::<Vec<_>>()
            })
            .sum::<usize>();

        assert_eq!(carried, 0);
    }

    #[test]
    fn a_generic_finalizer_gets_an_instance_for_its_receiver() {
        let mut program = Program::default();
        let generic = Ty::Named {
            id: crate::ty::TypeId(0),
            args: vec![Ty::Parameter("T".to_owned())],
        };
        let mut finalizer = Function::new(
            "Box.release".to_owned(),
            vec![generic.clone()],
            Ty::Unit,
            SPAN,
        );
        finalizer.type_params = vec!["T".to_owned()];
        let unit = finalizer.add_value(Ty::Unit);
        finalizer.block_mut(finalizer.entry).insts.push(Inst {
            result: Some(unit),
            kind: InstKind::Const(Const::Unit),
            span: SPAN,
        });
        finalizer.block_mut(finalizer.entry).term = Some(Terminator::Return(unit));
        let finalizer = program.add_function(finalizer);
        program.set_finalizer(generic, finalizer);

        let receiver = Ty::Named {
            id: crate::ty::TypeId(0),
            args: vec![Ty::INT],
        };
        let mut main = Function::new("main".to_owned(), Vec::new(), Ty::Unit, SPAN);
        let value = main.add_value(receiver.clone());
        main.block_mut(main.entry).insts.push(Inst {
            result: Some(value),
            kind: InstKind::MakeStruct {
                ty: receiver.clone(),
                fields: Vec::new(),
            },
            span: SPAN,
        });
        let unit = main.add_value(Ty::Unit);
        main.block_mut(main.entry).insts.push(Inst {
            result: Some(unit),
            kind: InstKind::Const(Const::Unit),
            span: SPAN,
        });
        main.block_mut(main.entry).term = Some(Terminator::Return(unit));
        program.add_function(main);

        run(&mut program);

        let instance = program.finalizer(&receiver).expect("a finalizer instance");
        assert!(!program.function(instance).is_template());
        assert_eq!(program.function(instance).params, [receiver]);
    }
}
