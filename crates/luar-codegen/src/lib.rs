//! Backend: LIR to machine code.

mod func;
mod link;
mod runtime;
mod ty;

use std::collections::HashMap;

use cranelift_codegen::Context;
use cranelift_codegen::ir::{AbiParam, InstBuilder, Signature, types};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId as ModuleFuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use luar_diagnostics::Span;
use luar_lir::program::{FuncId, Program};
use luar_lir::ty::Ty;

pub use crate::link::{LinkError, link};

use crate::func::{Translator, signature};
use crate::runtime::Handlers;
use crate::ty::machine;

/// Something the backend cannot emit yet, and the function it is in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Gap {
    pub function: String,
    pub span: Span,
    pub what: String,
}

/// An emitted object file, and what the backend could not put in it.
#[derive(Debug)]
pub struct Object {
    pub bytes: Vec<u8>,
    /// Empty for a program the backend emitted completely. Anything here
    /// means the machine code does less than the LIR describes.
    pub gaps: Vec<Gap>,
}

#[derive(Debug)]
pub enum Error {
    /// The host is a target Cranelift does not compile for.
    Target(String),
    /// Cranelift rejected what the translation built, which is a compiler bug
    /// rather than anything the source did.
    Cranelift(String),
    /// The program defines no `main` to start at (LR45).
    NoEntry,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Target(message) => write!(f, "no code generator for this target: {message}"),
            Self::Cranelift(message) => write!(f, "the backend built invalid code: {message}"),
            Self::NoEntry => f.write_str("the program exports no `main` (LR45)"),
        }
    }
}

impl std::error::Error for Error {}

/// Compiles `program` into an object file for the host.
///
/// # Errors
/// Returns [`Error`] where the host has no code generator, where the program
/// has no entrypoint, or where Cranelift rejects the emitted IR.
pub fn compile(program: &Program) -> Result<Object, Error> {
    let mut flags = settings::builder();
    // Cranelift's own verifier is what catches a translation bug, and the
    // cost of running it is small beside a wrong program.
    flags
        .set("enable_verifier", "true")
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    let flags = settings::Flags::new(flags);

    let isa = cranelift_native::builder()
        .map_err(|message| Error::Target(message.to_owned()))?
        .finish(flags)
        .map_err(|error| Error::Target(error.to_string()))?;
    let pointer = isa.pointer_type();
    let call_conv = isa.default_call_conv();

    let builder = ObjectBuilder::new(isa, "luar", cranelift_module::default_libcall_names())
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    let mut module = ObjectModule::new(builder);
    let handlers = Handlers::emit(&mut module, pointer, call_conv)?;
    let mut emitter = Emitter {
        program,
        module,
        pointer,
        call_conv,
        declared: HashMap::new(),
        handlers,
        gaps: Vec::new(),
    };
    emitter.declare()?;
    emitter.define()?;
    emitter.entry()?;

    let gaps = emitter.gaps;
    let bytes = emitter
        .module
        .finish()
        .emit()
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(Object { bytes, gaps })
}

struct Emitter<'a> {
    program: &'a Program,
    module: ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
    declared: HashMap<FuncId, ModuleFuncId>,
    handlers: Handlers,
    gaps: Vec<Gap>,
}

impl Emitter<'_> {
    /// Declares every function before any body is written, so that a call
    /// reaches one whatever order the two were emitted in.
    fn declare(&mut self) -> Result<(), Error> {
        for (id, function) in self.program.functions() {
            // LR19: a template is what a call instantiates, and
            // monomorphization has already written out every instance.
            if function.is_template() {
                continue;
            }
            let Some(signature) = signature(function, self.pointer, self.call_conv) else {
                let offending = function
                    .params
                    .iter()
                    .chain(std::iter::once(&function.result))
                    .find(|ty| machine(ty, self.pointer).is_none());
                self.gaps.push(Gap {
                    function: function.name.clone(),
                    span: function.span,
                    what: match offending {
                        Some(ty) => format!("a signature holding `{ty}`"),
                        None => "this signature".to_owned(),
                    },
                });
                continue;
            };
            let declared = self
                .module
                .declare_function(&symbol(id), Linkage::Local, &signature)
                .map_err(|error| Error::Cranelift(error.to_string()))?;
            self.declared.insert(id, declared);
        }
        Ok(())
    }

    fn define(&mut self) -> Result<(), Error> {
        let mut context = Context::new();
        let mut frame = FunctionBuilderContext::new();

        for (id, function) in self.program.functions() {
            let Some(&declared) = self.declared.get(&id) else {
                continue;
            };
            context.clear();
            context.func.signature = signature(function, self.pointer, self.call_conv)
                .expect("a declared function has a signature");

            // A call needs its callee in this function's reference table, and
            // that table is written before the builder takes the function.
            let mut callees = HashMap::new();
            for called in calls(function) {
                if let Some(&target) = self.declared.get(&called) {
                    let reference = self.module.declare_func_in_func(target, &mut context.func);
                    callees.insert(called, reference);
                }
            }

            let handlers = self
                .handlers
                .in_function(&mut self.module, &mut context.func);
            let translator = Translator {
                function,
                builder: FunctionBuilder::new(&mut context.func, &mut frame),
                pointer: self.pointer,
                callees,
                handlers,
                blocks: HashMap::new(),
                values: HashMap::new(),
                gaps: Vec::new(),
            };
            self.gaps.extend(translator.run());

            self.module
                .define_function(declared, &mut context)
                .map_err(rejected)?;
        }
        Ok(())
    }

    /// LR45: the C entrypoint the linker starts at, which runs `main` and
    /// turns what it returns into the process exit code.
    fn entry(&mut self) -> Result<(), Error> {
        let entry = self.program.entry.ok_or(Error::NoEntry)?;
        let main = self.program.function(entry);
        let Some(&declared) = self.declared.get(&entry) else {
            self.gaps.push(Gap {
                function: main.name.clone(),
                span: main.span,
                what: "an entrypoint returning `{}`".replace("{}", &main.result.to_string()),
            });
            return Ok(());
        };

        if !main.params.is_empty() {
            self.gaps.push(Gap {
                function: main.name.clone(),
                span: main.span,
                what: "an entrypoint that takes arguments".to_owned(),
            });
        }

        let mut signature = Signature::new(self.call_conv);
        signature.returns.push(AbiParam::new(types::I32));
        let shim = self
            .module
            .declare_function("main", Linkage::Export, &signature)
            .map_err(|error| Error::Cranelift(error.to_string()))?;

        let mut context = Context::new();
        let mut frame = FunctionBuilderContext::new();
        context.func.signature = signature;
        let reference = self
            .module
            .declare_func_in_func(declared, &mut context.func);

        let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.seal_block(block);

        let called = builder.ins().call(reference, &[]);
        let returned = builder.inst_results(called).first().copied();
        // LR45: an entrypoint that returns an integer maps it to the exit
        // code, and one that returns nothing exits successfully.
        let status = match (returned, exit_code_type(&main.result, self.pointer)) {
            (Some(value), Some(width)) if width == types::I32 => value,
            (Some(value), Some(width)) if width.bits() > 32 => {
                builder.ins().ireduce(types::I32, value)
            }
            (Some(value), Some(width)) if width.bits() < 32 => {
                builder.ins().sextend(types::I32, value)
            }
            _ => builder.ins().iconst(types::I32, 0),
        };
        builder.ins().return_(&[status]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(shim, &mut context)
            .map_err(rejected)
    }
}

/// The verifier keeps its findings in the error rather than in its message,
/// and those findings are the whole of what a translation bug looks like.
fn rejected(error: cranelift_module::ModuleError) -> Error {
    if let cranelift_module::ModuleError::Compilation(cranelift_codegen::CodegenError::Verifier(
        errors,
    )) = &error
    {
        return Error::Cranelift(errors.to_string());
    }
    Error::Cranelift(error.to_string())
}

/// The width `main` returns its exit code in, or `None` where it returns
/// something that is not one (LR45).
fn exit_code_type(result: &Ty, pointer: types::Type) -> Option<types::Type> {
    match result {
        Ty::Int(_) => machine(result, pointer),
        _ => None,
    }
}

/// Every function a body calls directly.
fn calls(function: &luar_lir::program::Function) -> Vec<FuncId> {
    let mut found = Vec::new();
    for (_, block) in function.blocks() {
        for inst in &block.insts {
            if let luar_lir::inst::InstKind::Call { callee, .. } = &inst.kind
                && !found.contains(callee)
            {
                found.push(*callee);
            }
        }
    }
    found
}

/// The symbol a function is emitted under. LIR names carry the path they came
/// from, which is not a symbol, so the id is what stays unique.
fn symbol(id: FuncId) -> String {
    format!("luar_f{}", id.0)
}
