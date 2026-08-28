//! Backend: LIR to machine code.

mod func;
mod gc;
mod layout;
mod link;
mod map;
mod runtime;
mod ty;

use std::collections::HashMap;

use cranelift_codegen::Context;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    AbiParam, GlobalValue, InstBuilder, MemFlags, Signature, TrapCode, types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId as ModuleFuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use luar_diagnostics::Span;
use luar_lir::inst::{Const, InstKind};
use luar_lir::program::{FuncId, Function, Program, Shape};
use luar_lir::ty::{Ty, TypeId};

pub use crate::link::{LinkError, link};

use crate::func::{Translator, signature};
use crate::runtime::Runtime;
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
    let runtime = Runtime::emit(&mut module, pointer, call_conv)?;
    let mut emitter = Emitter {
        program,
        module,
        pointer,
        call_conv,
        declared: HashMap::new(),
        runtime,
        texts: HashMap::new(),
        names: HashMap::new(),
        descriptors: HashMap::new(),
        vtables: HashMap::new(),
        gaps: Vec::new(),
    };
    emitter.declare()?;
    emitter.constants()?;
    emitter.dynamics()?;
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
    runtime: Runtime,
    /// One data object per distinct literal text, by its bytes.
    texts: HashMap<Vec<u8>, DataId>,
    /// Function names stored for runtime backtraces.
    names: HashMap<FuncId, DataId>,
    /// One object per type a dynamic value can say it holds. Its address is
    /// the type's identity, which is what a type test compares (LR25.3).
    descriptors: HashMap<Ty, DataId>,
    /// The method table of each implementation an interface value can carry,
    /// by the interface and the implementing type (LR18.1).
    vtables: HashMap<(TypeId, Ty), DataId>,
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
            let (name, linkage) = match &function.external {
                Some(symbol) => (symbol.clone(), Linkage::Import),
                None => (symbol(id), Linkage::Local),
            };
            let declared = self
                .module
                .declare_function(&name, linkage, &signature)
                .map_err(|error| Error::Cranelift(error.to_string()))?;
            self.declared.insert(id, declared);
        }
        Ok(())
    }

    /// Writes every string and byte-string literal into the object. Two
    /// literals spelling the same text share one, which they can because a
    /// string is immutable (LR4.5).
    fn constants(&mut self) -> Result<(), Error> {
        let mut texts = Vec::new();
        for (_, function) in self.program.functions() {
            for bytes in literals(function) {
                if !texts.contains(&bytes) {
                    texts.push(bytes);
                }
            }
        }

        for (index, bytes) in texts.into_iter().enumerate() {
            let mut stored = i64::try_from(bytes.len())
                .unwrap_or(0)
                .to_le_bytes()
                .to_vec();
            stored.extend_from_slice(&bytes);

            let mut description = DataDescription::new();
            description.define(stored.into_boxed_slice());
            let data = self
                .module
                .declare_data(&format!("luar_text{index}"), Linkage::Local, false, false)
                .map_err(|error| Error::Cranelift(error.to_string()))?;
            self.module
                .define_data(data, &description)
                .map_err(|error| Error::Cranelift(error.to_string()))?;
            self.texts.insert(bytes, data);
        }

        for (id, function) in self.program.functions() {
            if function.is_template() || function.external.is_some() {
                continue;
            }
            let mut description = DataDescription::new();
            description.define(
                backtrace_name(&function.name)
                    .as_bytes()
                    .to_vec()
                    .into_boxed_slice(),
            );
            let data = self
                .module
                .declare_data(
                    &format!("luar_function_name{}", id.0),
                    Linkage::Local,
                    false,
                    false,
                )
                .map_err(|error| Error::Cranelift(error.to_string()))?;
            self.module
                .define_data(data, &description)
                .map_err(|error| Error::Cranelift(error.to_string()))?;
            self.names.insert(id, data);
        }
        Ok(())
    }

    fn dynamics(&mut self) -> Result<(), Error> {
        let mut identities: Vec<Ty> = Vec::new();
        let mut tables: Vec<(TypeId, Ty)> = Vec::new();
        for (_, function) in self.program.functions() {
            if function.is_template() {
                continue;
            }
            for (_, block) in function.blocks() {
                for inst in &block.insts {
                    match &inst.kind {
                        InstKind::MakeDyn {
                            interface: None,
                            value,
                        } => {
                            let ty = function.type_of(*value).clone();
                            if !identities.contains(&ty) {
                                identities.push(ty);
                            }
                        }
                        InstKind::IsType { ty, .. } => {
                            if !identities.contains(ty) {
                                identities.push(ty.clone());
                            }
                        }
                        InstKind::MakeDyn {
                            interface: Some(interface),
                            value,
                        } => {
                            let key = (*interface, function.type_of(*value).clone());
                            if !tables.contains(&key) {
                                tables.push(key);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        for (index, ty) in identities.into_iter().enumerate() {
            let mut description = DataDescription::new();
            let index = u64::try_from(index).unwrap_or(u64::MAX);
            description.define(index.to_le_bytes().to_vec().into_boxed_slice());
            let data = self
                .module
                .declare_data(&format!("luar_type{index}"), Linkage::Local, false, false)
                .map_err(|error| Error::Cranelift(error.to_string()))?;
            self.module
                .define_data(data, &description)
                .map_err(|error| Error::Cranelift(error.to_string()))?;
            self.descriptors.insert(ty, data);
        }

        let cell = self.pointer.bytes() as usize;
        for (index, (interface, ty)) in tables.into_iter().enumerate() {
            let Ty::Named { id, .. } = &ty else {
                continue;
            };
            let Shape::Interface(shape) = &self.program.nominal(interface).shape else {
                continue;
            };
            let Some(implementation) = shape.implementors.iter().find(|held| held.ty == *id) else {
                continue;
            };
            let declared: Option<Vec<ModuleFuncId>> = implementation
                .methods
                .iter()
                .map(|function| self.declared.get(function).copied())
                .collect();
            let Some(declared) = declared else {
                continue;
            };

            let mut description = DataDescription::new();
            description.define(vec![0; (declared.len() * cell).max(cell)].into_boxed_slice());
            for (slot, function) in declared.into_iter().enumerate() {
                let reference = self.module.declare_func_in_data(function, &mut description);
                let offset = u32::try_from(slot * cell).expect("method table fits in u32");
                description.write_function_addr(offset, reference);
            }
            let data = self
                .module
                .declare_data(&format!("luar_vtable{index}"), Linkage::Local, false, false)
                .map_err(|error| Error::Cranelift(error.to_string()))?;
            self.module
                .define_data(data, &description)
                .map_err(|error| Error::Cranelift(error.to_string()))?;
            self.vtables.insert((interface, ty), data);
        }
        Ok(())
    }

    fn define(&mut self) -> Result<(), Error> {
        let mut context = Context::new();
        let mut frame = FunctionBuilderContext::new();

        for (id, function) in self.program.functions() {
            if function.external.is_some() {
                continue;
            }
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

            let mut texts: HashMap<Vec<u8>, GlobalValue> = HashMap::new();
            for bytes in literals(function) {
                if let Some(&data) = self.texts.get(&bytes) {
                    let value = self.module.declare_data_in_func(data, &mut context.func);
                    texts.insert(bytes, value);
                }
            }
            let descriptors: HashMap<Ty, GlobalValue> = self
                .descriptors
                .iter()
                .map(|(ty, data)| {
                    let value = self.module.declare_data_in_func(*data, &mut context.func);
                    (ty.clone(), value)
                })
                .collect();
            let vtables: HashMap<(TypeId, Ty), GlobalValue> = self
                .vtables
                .iter()
                .map(|(key, data)| {
                    let value = self.module.declare_data_in_func(*data, &mut context.func);
                    (key.clone(), value)
                })
                .collect();
            let function_name = self
                .module
                .declare_data_in_func(self.names[&id], &mut context.func);
            let function_name_length = backtrace_name(&function.name).len();

            let handlers = self
                .runtime
                .handlers_in(&mut self.module, &mut context.func);
            let allocate = self
                .runtime
                .allocate_in(&mut self.module, &mut context.func);
            let concat = self.runtime.concat_in(&mut self.module, &mut context.func);
            let text_equal = self
                .runtime
                .text_equal_in(&mut self.module, &mut context.func);
            let hash_bytes = self
                .runtime
                .hash_bytes_in(&mut self.module, &mut context.func);
            let display_signed = self
                .runtime
                .display_signed_in(&mut self.module, &mut context.func);
            let display_unsigned = self
                .runtime
                .display_unsigned_in(&mut self.module, &mut context.func);
            let abort = self.runtime.abort_in(&mut self.module, &mut context.func);
            let roots = self.runtime.roots_in(&mut self.module, &mut context.func);
            let finalizers = self
                .program
                .finalizers()
                .filter_map(|(ty, function)| {
                    let declared = self.declared.get(&function).copied()?;
                    let reference = self
                        .module
                        .declare_func_in_func(declared, &mut context.func);
                    Some((ty.clone(), reference))
                })
                .collect();
            let translator = Translator {
                program: self.program,
                function,
                function_name,
                function_name_length,
                builder: FunctionBuilder::new(&mut context.func, &mut frame),
                pointer: self.pointer,
                callees,
                texts,
                handlers,
                allocate,
                concat,
                text_equal,
                hash_bytes,
                display_signed,
                display_unsigned,
                abort,
                finalizers,
                roots,
                root_frame: None,
                root_offsets: HashMap::new(),
                temporary_roots: Vec::new(),
                blocks: HashMap::new(),
                values: HashMap::new(),
                slots: HashMap::new(),
                descriptors,
                vtables,
                gaps: Vec::new(),
            };
            self.gaps.extend(translator.run());

            self.module
                .define_function(declared, &mut context)
                .map_err(rejected)?;
        }
        Ok(())
    }

    /// LR45, LR78: the C entrypoint runs module initialization, then `main`,
    /// and turns what `main` returns into the process exit code.
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
        let initializers = self
            .program
            .initializers
            .iter()
            .filter_map(|initializer| self.declared.get(initializer))
            .map(|initializer| {
                self.module
                    .declare_func_in_func(*initializer, &mut context.func)
            })
            .collect::<Vec<_>>();

        let abort = self.runtime.abort_in(&mut self.module, &mut context.func);

        let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
        let block = builder.create_block();
        builder.switch_to_block(block);

        for initializer in initializers {
            builder.ins().call(initializer, &[]);
        }
        let called = builder.ins().call(reference, &[]);
        let mut returned = builder.inst_results(called).first().copied();
        let mut result = main.result.clone();

        // LR25.3: an exception escaping `main` reports the error and exits
        // unsuccessfully. One that can throw gives back what it returned or
        // what it threw, and only the first is an exit code.
        if let (Some(value), Some(inner)) = (returned, thrown_from(&main.result)) {
            let ran = builder.create_block();
            let threw = builder.create_block();
            let tag = builder
                .ins()
                .load(layout::TAG_TYPE, MemFlags::trusted(), value, layout::TAG);
            let failed = builder.ins().icmp_imm(IntCC::NotEqual, tag, 0);
            builder.ins().brif(failed, threw, &[], ran, &[]);

            builder.switch_to_block(threw);
            let kind = builder.ins().iconst(types::I8, UNCAUGHT_EXCEPTION);
            let none = builder.ins().iconst(self.pointer, 0);
            builder.ins().call(abort, &[kind, none]);
            builder.ins().trap(TrapCode::unwrap_user(1));

            builder.switch_to_block(ran);
            returned = exit_code_type(&inner, self.pointer).map(|width| {
                builder
                    .ins()
                    .load(width, MemFlags::trusted(), value, layout::CELL)
            });
            result = inner;
        }

        // LR45: an entrypoint that returns an integer maps it to the exit
        // code, and one that returns nothing exits successfully.
        let status = match (returned, exit_code_type(&result, self.pointer)) {
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

/// The abort kind `luar_abort` reports as an exception nothing caught.
const UNCAUGHT_EXCEPTION: i64 = 2;

/// What `main` returns where an exception can escape it: the type inside its
/// `Result<T, dynamic>` (LR25.3).
fn thrown_from(result: &Ty) -> Option<Ty> {
    match result {
        Ty::Builtin {
            kind: luar_lir::ty::Builtin::Result,
            args,
        } if args.get(1) == Some(&Ty::Dynamic) => args.first().cloned(),
        _ => None,
    }
}

/// The width `main` returns its exit code in, or `None` where it returns
/// something that is not one (LR45).
fn exit_code_type(result: &Ty, pointer: types::Type) -> Option<types::Type> {
    match result {
        Ty::Int(_) => machine(result, pointer),
        _ => None,
    }
}

/// Every string and byte-string literal a body holds.
fn literals(function: &Function) -> Vec<Vec<u8>> {
    let mut found = Vec::new();
    for (_, block) in function.blocks() {
        for inst in &block.insts {
            let bytes = match &inst.kind {
                luar_lir::inst::InstKind::Const(Const::Str(text)) => text.clone().into_bytes(),
                luar_lir::inst::InstKind::Const(Const::Bytes(bytes)) => bytes.clone(),
                _ => continue,
            };
            if !found.contains(&bytes) {
                found.push(bytes);
            }
        }
    }
    found
}

/// Every function a body calls directly.
fn calls(function: &luar_lir::program::Function) -> Vec<FuncId> {
    let mut found = Vec::new();
    for (_, block) in function.blocks() {
        for inst in &block.insts {
            let callee = match &inst.kind {
                luar_lir::inst::InstKind::Call { callee, .. } => *callee,
                luar_lir::inst::InstKind::MakeClosure { func, .. } => *func,
                _ => continue,
            };
            if !found.contains(&callee) {
                found.push(callee);
            }
        }
    }
    found
}

fn backtrace_name(name: &str) -> &str {
    name.rsplit('/').next().unwrap_or(name)
}

/// The symbol a function is emitted under. LIR names carry the path they came
/// from, which is not a symbol, so the id is what stays unique.
fn symbol(id: FuncId) -> String {
    format!("luar_f{}", id.0)
}
