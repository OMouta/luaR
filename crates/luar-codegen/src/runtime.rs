//! The handful of functions the emitted program needs at runtime.
//!
//! They are emitted into the same object rather than shipped as a library, so
//! a build needs a linker and a C runtime and nothing else.

use cranelift_codegen::Context;
use cranelift_codegen::ir::{AbiParam, FuncRef, InstBuilder, Signature, TrapCode, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, FuncId as ModuleFuncId, Linkage, Module};
use cranelift_object::ObjectModule;
use luar_lir::inst::Trap;

use crate::Error;
use crate::func::TRAPS;

/// The exit status a trapped program leaves with.
const TRAPPED: i64 = 101;

/// The file descriptor a trap reports on.
const STDERR: i64 = 2;

/// What the process does after `exit`, which never returns.
const AFTER_EXIT: TrapCode = TrapCode::unwrap_user(1);

/// The C runtime's unbuffered write. MSVC spells the POSIX name with an
/// underscore.
#[cfg(windows)]
const WRITE: &str = "_write";
#[cfg(not(windows))]
const WRITE: &str = "write";

/// One handler per trap kind, in [`TRAPS`] order.
pub(crate) struct Handlers {
    pub declared: [ModuleFuncId; TRAPS.len()],
}

impl Handlers {
    /// Emits a handler for every trap kind. Each writes which trap it was and
    /// exits, so a trapped program is told apart from one that ran (LR50).
    pub fn emit(
        module: &mut ObjectModule,
        pointer: types::Type,
        call_conv: CallConv,
    ) -> Result<Self, Error> {
        let mut exit = Signature::new(call_conv);
        exit.params.push(AbiParam::new(types::I32));
        let exit = module
            .declare_function("exit", Linkage::Import, &exit)
            .map_err(|error| Error::Cranelift(error.to_string()))?;

        let mut write = Signature::new(call_conv);
        write.params.push(AbiParam::new(types::I32));
        write.params.push(AbiParam::new(pointer));
        write.params.push(AbiParam::new(types::I32));
        write.returns.push(AbiParam::new(types::I32));
        let write = module
            .declare_function(WRITE, Linkage::Import, &write)
            .map_err(|error| Error::Cranelift(error.to_string()))?;

        let mut declared = Vec::with_capacity(TRAPS.len());
        for trap in TRAPS {
            declared.push(handler(module, pointer, call_conv, trap, exit, write)?);
        }
        Ok(Self {
            declared: declared
                .try_into()
                .expect("one handler was emitted per trap kind"),
        })
    }

    /// Puts every handler in `function`'s reference table.
    pub fn in_function(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> [FuncRef; TRAPS.len()] {
        self.declared
            .map(|declared| module.declare_func_in_func(declared, function))
    }
}

fn handler(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
    trap: Trap,
    exit: ModuleFuncId,
    write: ModuleFuncId,
) -> Result<ModuleFuncId, Error> {
    let message = format!("luar: trap: {}\n", trap.spelling());
    let mut description = DataDescription::new();
    description.define(message.clone().into_bytes().into_boxed_slice());
    let data = module
        .declare_data(
            &format!("luar_trap_{}", trap.spelling().replace('-', "_")),
            Linkage::Local,
            false,
            false,
        )
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    module
        .define_data(data, &description)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let signature = Signature::new(call_conv);
    let declared = module
        .declare_function(
            &format!("luar_trap_{}_handler", trap.spelling().replace('-', "_")),
            Linkage::Local,
            &signature,
        )
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let text = module.declare_data_in_func(data, &mut context.func);
    let write = module.declare_func_in_func(write, &mut context.func);
    let exit = module.declare_func_in_func(exit, &mut context.func);

    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let block = builder.create_block();
    builder.switch_to_block(block);

    let address = builder.ins().global_value(pointer, text);
    let length = builder
        .ins()
        .iconst(types::I32, i64::try_from(message.len()).unwrap_or(0));
    let stderr = builder.ins().iconst(types::I32, STDERR);
    builder.ins().call(write, &[stderr, address, length]);

    let status = builder.ins().iconst(types::I32, TRAPPED);
    builder.ins().call(exit, &[status]);
    builder.ins().trap(AFTER_EXIT);

    builder.seal_all_blocks();
    builder.finalize();

    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}
