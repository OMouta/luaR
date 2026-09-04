//! The handful of functions the emitted program needs at runtime.
//!
//! They are emitted into the same object rather than shipped as a library, so
//! a build needs a linker and a C runtime and nothing else.

use cranelift_codegen::Context;
use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::{AbiParam, FuncRef, InstBuilder, MemFlags, Signature, TrapCode, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId as ModuleFuncId, Linkage, Module};
use cranelift_object::ObjectModule;
use luar_lir::inst::Trap;

use crate::Error;
use crate::func::TRAPS;
use crate::gc;
use crate::map;

/// The exit status a trapped program leaves with.
const TRAPPED: i64 = 101;

/// The file descriptor a trap reports on.
const STDERR: i64 = 2;
const STDOUT: i64 = 1;

/// What the process does after `exit`, which never returns.
const AFTER_EXIT: TrapCode = TrapCode::unwrap_user(1);

/// The C runtime's unbuffered write. MSVC spells the POSIX name with an
/// underscore.
#[cfg(windows)]
const WRITE: &str = "_write";
#[cfg(not(windows))]
const WRITE: &str = "write";

#[cfg(windows)]
const GCVT: &str = "_gcvt";
#[cfg(not(windows))]
const GCVT: &str = "gcvt";

/// What the emitted program reaches at runtime.
pub(crate) struct Runtime {
    /// One handler per trap kind, in [`TRAPS`] order.
    pub handlers: [ModuleFuncId; TRAPS.len()],
    /// Where managed aggregate storage comes from (LR29).
    pub allocate: ModuleFuncId,
    pub collect: ModuleFuncId,
    pub slice_finalizer: ModuleFuncId,
    /// Primitive string operations (LR11.2, LR11.3, LR35).
    pub concat: ModuleFuncId,
    pub text_equal: ModuleFuncId,
    pub hash_bytes: ModuleFuncId,
    pub display_signed: ModuleFuncId,
    pub display_unsigned: ModuleFuncId,
    pub display_char: ModuleFuncId,
    pub display_f32: ModuleFuncId,
    pub display_f64: ModuleFuncId,
    pub power_f32: ModuleFuncId,
    pub power_f64: ModuleFuncId,
    pub print: ModuleFuncId,
    pub abort: ModuleFuncId,
    /// Builds the `List<string>` passed to an entrypoint (LR45).
    pub arguments: ModuleFuncId,
    /// The bucket a map holds a key in, and the bucket it will (LR13.2).
    pub map_find: ModuleFuncId,
    pub map_insert: ModuleFuncId,
    pub map_remove: ModuleFuncId,
    /// The most recently entered shadow-stack frame.
    roots: DataId,
}

impl Runtime {
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

        let collector = gc::emit(module, pointer, call_conv)?;
        let slice_finalizer = define_slice_finalizer(module, pointer, call_conv)?;
        let concat = define_concat(module, pointer, call_conv, collector.allocate)?;
        define_bytes_of(module, pointer, call_conv)?;
        define_string_from_bytes(module, pointer, call_conv, collector.allocate)?;
        define_math(module, call_conv)?;
        let text_equal = define_text_equal(module, pointer, call_conv)?;
        let hash_bytes = define_hash_bytes(module, pointer, call_conv)?;
        let display_signed =
            define_display_integer(module, pointer, call_conv, collector.allocate, true)?;
        let display_unsigned =
            define_display_integer(module, pointer, call_conv, collector.allocate, false)?;
        let display_char = define_display_char(module, pointer, call_conv, collector.allocate)?;
        let (gcvt, strtod, strlen) = declare_float_formatting(module, pointer, call_conv)?;
        let display_f32 = define_display_float(
            module,
            pointer,
            call_conv,
            collector.allocate,
            gcvt,
            strtod,
            strlen,
            types::F32,
            9,
        )?;
        let display_f64 = define_display_float(
            module,
            pointer,
            call_conv,
            collector.allocate,
            gcvt,
            strtod,
            strlen,
            types::F64,
            17,
        )?;
        let power_f32 = declare_power(module, call_conv, types::F32, "powf")?;
        let power_f64 = declare_power(module, call_conv, types::F64, "pow")?;
        let print = define_print(module, pointer, call_conv, write)?;
        let abort = define_abort(module, pointer, call_conv, exit, write, collector.roots)?;
        let arguments = define_arguments(module, pointer, call_conv)?;
        let table = map::emit(module, pointer, call_conv, collector.allocate, text_equal)?;

        let mut handlers = Vec::with_capacity(TRAPS.len());
        for trap in TRAPS {
            handlers.push(handler(module, pointer, call_conv, trap, exit, write)?);
        }
        Ok(Self {
            handlers: handlers
                .try_into()
                .expect("one handler was emitted per trap kind"),
            allocate: collector.allocate,
            collect: collector.collect,
            slice_finalizer,
            concat,
            text_equal,
            hash_bytes,
            display_signed,
            display_unsigned,
            display_char,
            display_f32,
            display_f64,
            power_f32,
            power_f64,
            print,
            abort,
            arguments,
            map_find: table.find,
            map_insert: table.insert,
            map_remove: table.remove,
            roots: collector.roots,
        })
    }

    pub fn map_find_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.map_find, function)
    }

    pub fn map_remove_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.map_remove, function)
    }

    pub fn map_insert_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.map_insert, function)
    }

    /// Puts every handler in `function`'s reference table.
    pub fn handlers_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> [FuncRef; TRAPS.len()] {
        self.handlers
            .map(|declared| module.declare_func_in_func(declared, function))
    }

    pub fn allocate_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.allocate, function)
    }

    pub fn collect_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.collect, function)
    }

    pub fn slice_finalizer_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.slice_finalizer, function)
    }

    pub fn concat_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.concat, function)
    }

    pub fn text_equal_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.text_equal, function)
    }

    pub fn hash_bytes_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.hash_bytes, function)
    }

    pub fn display_signed_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.display_signed, function)
    }

    pub fn display_char_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.display_char, function)
    }

    pub fn display_unsigned_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.display_unsigned, function)
    }

    pub fn display_f32_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.display_f32, function)
    }

    pub fn display_f64_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.display_f64, function)
    }

    pub fn power_f32_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.power_f32, function)
    }

    pub fn power_f64_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.power_f64, function)
    }

    pub fn print_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.print, function)
    }

    pub fn abort_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.abort, function)
    }

    pub fn arguments_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.arguments, function)
    }

    pub fn roots_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> cranelift_codegen::ir::GlobalValue {
        module.declare_data_in_func(self.roots, function)
    }
}

fn declare_power(
    module: &mut ObjectModule,
    call_conv: CallConv,
    ty: types::Type,
    name: &str,
) -> Result<ModuleFuncId, Error> {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(ty));
    signature.params.push(AbiParam::new(ty));
    signature.returns.push(AbiParam::new(ty));
    module
        .declare_function(name, Linkage::Import, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))
}

fn define_math(module: &mut ObjectModule, call_conv: CallConv) -> Result<(), Error> {
    for (luar, native) in [
        ("floor", "floor"),
        ("ceil", "ceil"),
        ("round", "round"),
        ("truncate", "trunc"),
        ("sqrt", "sqrt"),
        ("cbrt", "cbrt"),
        ("exp", "exp"),
        ("log", "log"),
        ("log2", "log2"),
        ("log10", "log10"),
        ("sin", "sin"),
        ("cos", "cos"),
        ("tan", "tan"),
        ("asin", "asin"),
        ("acos", "acos"),
        ("atan", "atan"),
    ] {
        define_math_function(module, call_conv, luar, native, 1)?;
    }
    define_math_function(module, call_conv, "atan2", "atan2", 2)?;
    Ok(())
}

fn define_math_function(
    module: &mut ObjectModule,
    call_conv: CallConv,
    luar: &str,
    native: &str,
    arity: usize,
) -> Result<ModuleFuncId, Error> {
    let mut signature = Signature::new(call_conv);
    for _ in 0..arity {
        signature.params.push(AbiParam::new(types::F64));
    }
    signature.returns.push(AbiParam::new(types::F64));

    let native = module
        .declare_function(native, Linkage::Import, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    let declared = module
        .declare_function(&format!("luar_{luar}"), Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let native = module.declare_func_in_func(native, &mut context.func);
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    let args = builder.block_params(entry).to_vec();
    let call = builder.ins().call(native, &args);
    let result = builder.inst_results(call)[0];
    builder.ins().return_(&[result]);
    builder.seal_all_blocks();
    builder.finalize();

    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

fn declare_float_formatting(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
) -> Result<(ModuleFuncId, ModuleFuncId, ModuleFuncId), Error> {
    let mut gcvt = Signature::new(call_conv);
    gcvt.params.push(AbiParam::new(types::F64));
    gcvt.params.push(AbiParam::new(types::I32));
    gcvt.params.push(AbiParam::new(pointer));
    gcvt.returns.push(AbiParam::new(pointer));
    let gcvt = module
        .declare_function(GCVT, Linkage::Import, &gcvt)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut strtod = Signature::new(call_conv);
    strtod.params.push(AbiParam::new(pointer));
    strtod.params.push(AbiParam::new(pointer));
    strtod.returns.push(AbiParam::new(types::F64));
    let strtod = module
        .declare_function("strtod", Linkage::Import, &strtod)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut strlen = Signature::new(call_conv);
    strlen.params.push(AbiParam::new(pointer));
    strlen.returns.push(AbiParam::new(pointer));
    let strlen = module
        .declare_function("strlen", Linkage::Import, &strlen)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok((gcvt, strtod, strlen))
}

#[allow(clippy::too_many_arguments)]
fn define_display_float(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
    allocate: ModuleFuncId,
    gcvt: ModuleFuncId,
    strtod: ModuleFuncId,
    strlen: ModuleFuncId,
    ty: types::Type,
    precision: u8,
) -> Result<ModuleFuncId, Error> {
    let suffix = if ty == types::F32 { "f32" } else { "f64" };
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(ty));
    signature.returns.push(AbiParam::new(pointer));
    let declared = module
        .declare_function(
            &format!("luar_display_{suffix}"),
            Linkage::Local,
            &signature,
        )
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let allocate = module.declare_func_in_func(allocate, &mut context.func);
    let gcvt = module.declare_func_in_func(gcvt, &mut context.func);
    let strtod = module.declare_func_in_func(strtod, &mut context.func);
    let strlen = module.declare_func_in_func(strlen, &mut context.func);
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let format = builder.create_block();
    let retry = builder.create_block();
    let done = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(format, types::I32);
    builder.switch_to_block(entry);

    let original = builder.block_params(entry)[0];
    let promoted = if ty == types::F32 {
        builder.ins().fpromote(types::F64, original)
    } else {
        original
    };
    let bytes = builder.ins().iconst(pointer, 48);
    let no_finalizer = builder.ins().iconst(pointer, 0);
    let call = builder.ins().call(allocate, &[bytes, no_finalizer]);
    let text = builder.inst_results(call)[0];
    let destination = builder.ins().iadd_imm(text, 8);
    let one = builder.ins().iconst(types::I32, 1);
    builder
        .ins()
        .jump(format, &[cranelift_codegen::ir::BlockArg::Value(one)]);

    builder.switch_to_block(format);
    let digits = builder.block_params(format)[0];
    builder.ins().call(gcvt, &[promoted, digits, destination]);
    let no_end = builder.ins().iconst(pointer, 0);
    let call = builder.ins().call(strtod, &[destination, no_end]);
    let parsed = builder.inst_results(call)[0];
    let parsed = if ty == types::F32 {
        builder.ins().fdemote(types::F32, parsed)
    } else {
        parsed
    };
    let same = builder.ins().fcmp(FloatCC::Equal, original, parsed);
    let last = builder
        .ins()
        .icmp_imm(IntCC::Equal, digits, i64::from(precision));
    let finished = builder.ins().bor(same, last);
    builder.ins().brif(finished, done, &[], retry, &[]);

    builder.switch_to_block(retry);
    let next = builder.ins().iadd_imm(digits, 1);
    builder
        .ins()
        .jump(format, &[cranelift_codegen::ir::BlockArg::Value(next)]);

    builder.switch_to_block(done);
    let call = builder.ins().call(strlen, &[destination]);
    let length = builder.inst_results(call)[0];
    let length = integer_width(&mut builder, length, types::I64);
    let last = builder.ins().iadd_imm(length, -1);
    let last = load_byte(&mut builder, text, last);
    let trailing_point = builder.ins().icmp_imm(IntCC::Equal, last, i64::from(b'.'));
    let without_point = builder.ins().iadd_imm(length, -1);
    let length = builder.ins().select(trailing_point, without_point, length);
    builder.ins().store(MemFlags::trusted(), length, text, 0);
    builder.ins().return_(&[text]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

fn define_slice_finalizer(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
) -> Result<ModuleFuncId, Error> {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(pointer));
    signature.returns.push(AbiParam::new(types::I8));
    let declared = module
        .declare_function("luar_slice_finalize", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    let slice = builder.block_params(entry)[0];
    let array_owner =
        builder
            .ins()
            .load(pointer, MemFlags::trusted(), slice, crate::layout::BORROWS);
    let release = builder.create_block();
    let done = builder.create_block();
    let is_array = builder.ins().icmp_imm(IntCC::NotEqual, array_owner, 0);
    builder.ins().brif(is_array, done, &[], release, &[]);
    builder.switch_to_block(release);
    let owner = builder
        .ins()
        .load(pointer, MemFlags::trusted(), slice, crate::layout::BUFFER);
    let borrows = builder
        .ins()
        .load(pointer, MemFlags::trusted(), owner, crate::layout::BORROWS);
    let remaining = builder.ins().iadd_imm(borrows, -1);
    builder.ins().store(
        MemFlags::trusted(),
        remaining,
        owner,
        crate::layout::BORROWS,
    );
    builder.ins().jump(done, &[]);
    builder.switch_to_block(done);
    let zero = builder.ins().iconst(types::I8, 0);
    builder.ins().return_(&[zero]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

/// Process arguments live for the life of the process (LR45).
fn define_arguments(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
) -> Result<ModuleFuncId, Error> {
    let mut malloc_signature = Signature::new(call_conv);
    malloc_signature.params.push(AbiParam::new(pointer));
    malloc_signature.returns.push(AbiParam::new(pointer));
    let malloc = module
        .declare_function("malloc", Linkage::Import, &malloc_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut strlen_signature = Signature::new(call_conv);
    strlen_signature.params.push(AbiParam::new(pointer));
    strlen_signature.returns.push(AbiParam::new(pointer));
    let strlen = module
        .declare_function("strlen", Linkage::Import, &strlen_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut memcpy_signature = Signature::new(call_conv);
    memcpy_signature.params.push(AbiParam::new(pointer));
    memcpy_signature.params.push(AbiParam::new(pointer));
    memcpy_signature.params.push(AbiParam::new(pointer));
    memcpy_signature.returns.push(AbiParam::new(pointer));
    let memcpy = module
        .declare_function("memcpy", Linkage::Import, &memcpy_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(types::I32));
    signature.params.push(AbiParam::new(pointer));
    signature.returns.push(AbiParam::new(pointer));
    let declared = module
        .declare_function("luar_arguments", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let malloc = module.declare_func_in_func(malloc, &mut context.func);
    let strlen = module.declare_func_in_func(strlen, &mut context.func);
    let memcpy = module.declare_func_in_func(memcpy, &mut context.func);
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let copy = builder.create_block();
    let copy_one = builder.create_block();
    let done = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(copy, types::I32);

    builder.switch_to_block(entry);
    let argc = builder.block_params(entry)[0];
    let argv = builder.block_params(entry)[1];
    let count = builder.ins().uextend(pointer, argc);
    let header_bytes = builder.ins().iconst(
        pointer,
        i64::from(crate::layout::COLLECTION_CELLS * pointer.bytes()),
    );
    let call = builder.ins().call(malloc, &[header_bytes]);
    let list = builder.inst_results(call)[0];
    let buffer_bytes = builder.ins().imul_imm(count, i64::from(pointer.bytes()));
    let call = builder.ins().call(malloc, &[buffer_bytes]);
    let buffer = builder.inst_results(call)[0];
    builder
        .ins()
        .store(MemFlags::trusted(), count, list, crate::layout::LENGTH);
    builder
        .ins()
        .store(MemFlags::trusted(), count, list, crate::layout::CAPACITY);
    builder
        .ins()
        .store(MemFlags::trusted(), buffer, list, crate::layout::BUFFER);
    let no_borrows = builder.ins().iconst(pointer, 0);
    builder.ins().store(
        MemFlags::trusted(),
        no_borrows,
        list,
        crate::layout::BORROWS,
    );
    let zero = builder.ins().iconst(types::I32, 0);
    builder
        .ins()
        .jump(copy, &[cranelift_codegen::ir::BlockArg::Value(zero)]);

    builder.switch_to_block(copy);
    let index = builder.block_params(copy)[0];
    let more = builder.ins().icmp(IntCC::UnsignedLessThan, index, argc);
    builder.ins().brif(more, copy_one, &[], done, &[]);

    builder.switch_to_block(copy_one);
    let offset = builder.ins().uextend(pointer, index);
    let offset = builder.ins().imul_imm(offset, i64::from(pointer.bytes()));
    let source = builder.ins().iadd(argv, offset);
    let source = builder.ins().load(pointer, MemFlags::trusted(), source, 0);
    let call = builder.ins().call(strlen, &[source]);
    let length = builder.inst_results(call)[0];
    let bytes = builder
        .ins()
        .iadd_imm(length, i64::from(crate::layout::CELL));
    let call = builder.ins().call(malloc, &[bytes]);
    let string = builder.inst_results(call)[0];
    builder.ins().store(MemFlags::trusted(), length, string, 0);
    let text = builder
        .ins()
        .iadd_imm(string, i64::from(crate::layout::CELL));
    builder.ins().call(memcpy, &[text, source, length]);
    let cell = builder.ins().iadd(buffer, offset);
    builder.ins().store(MemFlags::trusted(), string, cell, 0);
    let next = builder.ins().iadd_imm(index, 1);
    builder
        .ins()
        .jump(copy, &[cranelift_codegen::ir::BlockArg::Value(next)]);

    builder.switch_to_block(done);
    builder.ins().return_(&[list]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

fn define_print(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
    write: ModuleFuncId,
) -> Result<ModuleFuncId, Error> {
    let newline = static_data(module, "luar_print_newline", b"\n")?;
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(pointer));
    let declared = module
        .declare_function("luar_print", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let write = module.declare_func_in_func(write, &mut context.func);
    let newline = module.declare_data_in_func(newline, &mut context.func);
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);

    let text = builder.block_params(entry)[0];
    let length = builder.ins().load(types::I64, MemFlags::trusted(), text, 0);
    let length = if pointer.bits() > 32 {
        builder.ins().ireduce(types::I32, length)
    } else {
        length
    };
    let bytes = builder.ins().iadd_imm(text, 8);
    let stdout = builder.ins().iconst(types::I32, STDOUT);
    builder.ins().call(write, &[stdout, bytes, length]);
    let newline = builder.ins().global_value(pointer, newline);
    let one = builder.ins().iconst(types::I32, 1);
    builder.ins().call(write, &[stdout, newline, one]);
    builder.ins().return_(&[]);

    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

fn define_concat(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
    allocate: ModuleFuncId,
) -> Result<ModuleFuncId, Error> {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(pointer));
    signature.returns.push(AbiParam::new(pointer));
    let declared = module
        .declare_function("luar_string_concat", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let allocate = module.declare_func_in_func(allocate, &mut context.func);
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let copy_left = builder.create_block();
    let copy_left_byte = builder.create_block();
    let copy_right = builder.create_block();
    let copy_right_byte = builder.create_block();
    let done = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(copy_left, types::I64);
    builder.append_block_param(copy_left_byte, types::I64);
    builder.append_block_param(copy_right, types::I64);
    builder.append_block_param(copy_right_byte, types::I64);

    builder.switch_to_block(entry);
    let left = builder.block_params(entry)[0];
    let right = builder.block_params(entry)[1];
    let left_len = builder.ins().load(types::I64, MemFlags::trusted(), left, 0);
    let right_len = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), right, 0);
    let length = builder.ins().iadd(left_len, right_len);
    let cell = i64::from(pointer.bytes());
    let bytes = builder.ins().iadd_imm(length, 8 + cell - 1);
    let bytes = builder.ins().band_imm(bytes, -cell);
    let bytes = integer_width(&mut builder, bytes, pointer);
    let no_finalizer = builder.ins().iconst(pointer, 0);
    let call = builder.ins().call(allocate, &[bytes, no_finalizer]);
    let string = builder.inst_results(call)[0];
    builder.ins().store(MemFlags::trusted(), length, string, 0);
    let zero = builder.ins().iconst(types::I64, 0);
    builder
        .ins()
        .jump(copy_left, &[cranelift_codegen::ir::BlockArg::Value(zero)]);

    builder.switch_to_block(copy_left);
    let index = builder.block_params(copy_left)[0];
    let more = builder.ins().icmp(IntCC::UnsignedLessThan, index, left_len);
    builder.ins().brif(
        more,
        copy_left_byte,
        &[cranelift_codegen::ir::BlockArg::Value(index)],
        copy_right,
        &[cranelift_codegen::ir::BlockArg::Value(zero)],
    );

    builder.switch_to_block(copy_left_byte);
    let index = builder.block_params(copy_left_byte)[0];
    copy_byte(&mut builder, left, index, string, index);
    let next = builder.ins().iadd_imm(index, 1);
    builder
        .ins()
        .jump(copy_left, &[cranelift_codegen::ir::BlockArg::Value(next)]);

    builder.switch_to_block(copy_right);
    let index = builder.block_params(copy_right)[0];
    let more = builder
        .ins()
        .icmp(IntCC::UnsignedLessThan, index, right_len);
    builder.ins().brif(
        more,
        copy_right_byte,
        &[cranelift_codegen::ir::BlockArg::Value(index)],
        done,
        &[],
    );

    builder.switch_to_block(copy_right_byte);
    let index = builder.block_params(copy_right_byte)[0];
    let destination = builder.ins().iadd(left_len, index);
    copy_byte(&mut builder, right, index, string, destination);
    let next = builder.ins().iadd_imm(index, 1);
    builder
        .ins()
        .jump(copy_right, &[cranelift_codegen::ir::BlockArg::Value(next)]);

    builder.switch_to_block(done);
    builder.ins().return_(&[string]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

/// `std/mem.bytesOf`, reached by name through `luar_sema::check::runtime_symbol`
/// (LR60, LR72).
fn define_bytes_of(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
) -> Result<(), Error> {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(pointer));
    signature.returns.push(AbiParam::new(pointer));
    let declared = module
        .declare_function("luar_bytes_of", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    let text = builder.block_params(entry)[0];
    let bytes = builder.ins().iadd_imm(text, 8);
    builder.ins().return_(&[bytes]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(())
}

/// `std/mem.stringFromBytes`, reached by name through
/// `luar_sema::check::runtime_symbol` (LR60, LR72).
fn define_string_from_bytes(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
    allocate: ModuleFuncId,
) -> Result<(), Error> {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(types::I64));
    signature.returns.push(AbiParam::new(pointer));
    let declared = module
        .declare_function("luar_string_from_bytes", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let allocate = module.declare_func_in_func(allocate, &mut context.func);
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let copy = builder.create_block();
    let copy_byte = builder.create_block();
    let done = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(copy, types::I64);
    builder.append_block_param(copy_byte, types::I64);

    builder.switch_to_block(entry);
    let data = builder.block_params(entry)[0];
    let length = builder.block_params(entry)[1];
    let cell = i64::from(pointer.bytes());
    let bytes = builder.ins().iadd_imm(length, 8 + cell - 1);
    let bytes = builder.ins().band_imm(bytes, -cell);
    let bytes = integer_width(&mut builder, bytes, pointer);
    let no_finalizer = builder.ins().iconst(pointer, 0);
    let call = builder.ins().call(allocate, &[bytes, no_finalizer]);
    let string = builder.inst_results(call)[0];
    builder.ins().store(MemFlags::trusted(), length, string, 0);
    let zero = builder.ins().iconst(types::I64, 0);
    builder
        .ins()
        .jump(copy, &[cranelift_codegen::ir::BlockArg::Value(zero)]);

    builder.switch_to_block(copy);
    let index = builder.block_params(copy)[0];
    let more = builder.ins().icmp(IntCC::UnsignedLessThan, index, length);
    builder.ins().brif(
        more,
        copy_byte,
        &[cranelift_codegen::ir::BlockArg::Value(index)],
        done,
        &[],
    );

    builder.switch_to_block(copy_byte);
    let index = builder.block_params(copy_byte)[0];
    let from = builder.ins().iadd(data, index);
    let byte = builder.ins().load(types::I8, MemFlags::trusted(), from, 0);
    let start = builder.ins().iadd_imm(string, 8);
    let to = builder.ins().iadd(start, index);
    builder.ins().store(MemFlags::trusted(), byte, to, 0);
    let next = builder.ins().iadd_imm(index, 1);
    builder
        .ins()
        .jump(copy, &[cranelift_codegen::ir::BlockArg::Value(next)]);

    builder.switch_to_block(done);
    builder.ins().return_(&[string]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(())
}

fn define_text_equal(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
) -> Result<ModuleFuncId, Error> {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(pointer));
    signature.returns.push(AbiParam::new(types::I8));
    let declared = module
        .declare_function("luar_text_equal", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let compare = builder.create_block();
    let compare_byte = builder.create_block();
    let same = builder.create_block();
    let different = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(compare, types::I64);
    builder.append_block_param(compare_byte, types::I64);

    builder.switch_to_block(entry);
    let left = builder.block_params(entry)[0];
    let right = builder.block_params(entry)[1];
    let left_len = builder.ins().load(types::I64, MemFlags::trusted(), left, 0);
    let right_len = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), right, 0);
    let lengths_match = builder.ins().icmp(IntCC::Equal, left_len, right_len);
    let zero = builder.ins().iconst(types::I64, 0);
    builder.ins().brif(
        lengths_match,
        compare,
        &[cranelift_codegen::ir::BlockArg::Value(zero)],
        different,
        &[],
    );

    builder.switch_to_block(compare);
    let index = builder.block_params(compare)[0];
    let more = builder.ins().icmp(IntCC::UnsignedLessThan, index, left_len);
    builder.ins().brif(
        more,
        compare_byte,
        &[cranelift_codegen::ir::BlockArg::Value(index)],
        same,
        &[],
    );

    builder.switch_to_block(compare_byte);
    let index = builder.block_params(compare_byte)[0];
    let a = load_byte(&mut builder, left, index);
    let b = load_byte(&mut builder, right, index);
    let matches = builder.ins().icmp(IntCC::Equal, a, b);
    let next = builder.ins().iadd_imm(index, 1);
    builder.ins().brif(
        matches,
        compare,
        &[cranelift_codegen::ir::BlockArg::Value(next)],
        different,
        &[],
    );

    builder.switch_to_block(same);
    let one = builder.ins().iconst(types::I8, 1);
    builder.ins().return_(&[one]);

    builder.switch_to_block(different);
    let zero = builder.ins().iconst(types::I8, 0);
    builder.ins().return_(&[zero]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

fn define_hash_bytes(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
) -> Result<ModuleFuncId, Error> {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(pointer));
    signature.returns.push(AbiParam::new(types::I64));
    let declared = module
        .declare_function("luar_hash_bytes", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let hash = builder.create_block();
    let hash_byte = builder.create_block();
    let done = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(hash, types::I64);
    builder.append_block_param(hash, types::I64);
    builder.append_block_param(hash_byte, types::I64);
    builder.append_block_param(hash_byte, types::I64);
    builder.append_block_param(done, types::I64);

    builder.switch_to_block(entry);
    let text = builder.block_params(entry)[0];
    let length = builder.ins().load(types::I64, MemFlags::trusted(), text, 0);
    let zero = builder.ins().iconst(types::I64, 0);
    let basis = builder
        .ins()
        .iconst(types::I64, 0xcbf29ce484222325_u64 as i64);
    builder.ins().jump(
        hash,
        &[
            cranelift_codegen::ir::BlockArg::Value(zero),
            cranelift_codegen::ir::BlockArg::Value(basis),
        ],
    );

    builder.switch_to_block(hash);
    let index = builder.block_params(hash)[0];
    let value = builder.block_params(hash)[1];
    let more = builder.ins().icmp(IntCC::UnsignedLessThan, index, length);
    builder.ins().brif(
        more,
        hash_byte,
        &[
            cranelift_codegen::ir::BlockArg::Value(index),
            cranelift_codegen::ir::BlockArg::Value(value),
        ],
        done,
        &[cranelift_codegen::ir::BlockArg::Value(value)],
    );

    builder.switch_to_block(hash_byte);
    let index = builder.block_params(hash_byte)[0];
    let value = builder.block_params(hash_byte)[1];
    let byte = load_byte(&mut builder, text, index);
    let byte = builder.ins().uextend(types::I64, byte);
    let value = builder.ins().bxor(value, byte);
    let value = builder.ins().imul_imm(value, 0x100000001b3);
    let next = builder.ins().iadd_imm(index, 1);
    builder.ins().jump(
        hash,
        &[
            cranelift_codegen::ir::BlockArg::Value(next),
            cranelift_codegen::ir::BlockArg::Value(value),
        ],
    );

    builder.switch_to_block(done);
    let value = builder.block_params(done)[0];
    builder.ins().return_(&[value]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

fn define_display_integer(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
    allocate: ModuleFuncId,
    signed: bool,
) -> Result<ModuleFuncId, Error> {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(types::I64));
    signature.returns.push(AbiParam::new(pointer));
    let suffix = if signed { "i64" } else { "u64" };
    let declared = module
        .declare_function(
            &format!("luar_display_{suffix}"),
            Linkage::Local,
            &signature,
        )
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let allocate = module.declare_func_in_func(allocate, &mut context.func);
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let count = builder.create_block();
    let count_more = builder.create_block();
    let build = builder.create_block();
    let write = builder.create_block();
    let write_more = builder.create_block();
    let done = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(count, types::I64);
    builder.append_block_param(count, types::I64);
    builder.append_block_param(count_more, types::I64);
    builder.append_block_param(count_more, types::I64);
    builder.append_block_param(build, types::I64);
    builder.append_block_param(write, types::I64);
    builder.append_block_param(write, types::I64);
    builder.append_block_param(write, pointer);
    builder.append_block_param(write_more, types::I64);
    builder.append_block_param(write_more, types::I64);
    builder.append_block_param(write_more, pointer);
    builder.append_block_param(done, pointer);

    builder.switch_to_block(entry);
    let value = builder.block_params(entry)[0];
    let negative = if signed {
        let zero = builder.ins().iconst(types::I64, 0);
        builder.ins().icmp(IntCC::SignedLessThan, value, zero)
    } else {
        builder.ins().iconst(types::I8, 0)
    };
    let magnitude = if signed {
        let negated = builder.ins().ineg(value);
        builder.ins().select(negative, negated, value)
    } else {
        value
    };
    let one = builder.ins().iconst(types::I64, 1);
    builder.ins().jump(
        count,
        &[
            cranelift_codegen::ir::BlockArg::Value(magnitude),
            cranelift_codegen::ir::BlockArg::Value(one),
        ],
    );

    builder.switch_to_block(count);
    let remaining = builder.block_params(count)[0];
    let digits = builder.block_params(count)[1];
    let ten = builder.ins().iconst(types::I64, 10);
    let more = builder
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, remaining, ten);
    builder.ins().brif(
        more,
        count_more,
        &[
            cranelift_codegen::ir::BlockArg::Value(remaining),
            cranelift_codegen::ir::BlockArg::Value(digits),
        ],
        build,
        &[cranelift_codegen::ir::BlockArg::Value(digits)],
    );

    builder.switch_to_block(count_more);
    let remaining = builder.block_params(count_more)[0];
    let digits = builder.block_params(count_more)[1];
    let ten = builder.ins().iconst(types::I64, 10);
    let remaining = builder.ins().udiv(remaining, ten);
    let digits = builder.ins().iadd_imm(digits, 1);
    builder.ins().jump(
        count,
        &[
            cranelift_codegen::ir::BlockArg::Value(remaining),
            cranelift_codegen::ir::BlockArg::Value(digits),
        ],
    );

    builder.switch_to_block(build);
    let digits = builder.block_params(build)[0];
    let sign = builder.ins().uextend(types::I64, negative);
    let length = builder.ins().iadd(digits, sign);
    let cell = i64::from(pointer.bytes());
    let bytes = builder.ins().iadd_imm(length, 8 + cell - 1);
    let bytes = builder.ins().band_imm(bytes, -cell);
    let bytes = integer_width(&mut builder, bytes, pointer);
    let no_finalizer = builder.ins().iconst(pointer, 0);
    let call = builder.ins().call(allocate, &[bytes, no_finalizer]);
    let string = builder.inst_results(call)[0];
    builder.ins().store(MemFlags::trusted(), length, string, 0);
    if signed {
        let sign_block = builder.create_block();
        let number_block = builder.create_block();
        builder
            .ins()
            .brif(negative, sign_block, &[], number_block, &[]);
        builder.switch_to_block(sign_block);
        let minus = builder.ins().iconst(types::I8, i64::from(b'-'));
        builder.ins().store(MemFlags::trusted(), minus, string, 8);
        builder.ins().jump(number_block, &[]);
        builder.switch_to_block(number_block);
    }
    builder.ins().jump(
        write,
        &[
            cranelift_codegen::ir::BlockArg::Value(magnitude),
            cranelift_codegen::ir::BlockArg::Value(digits),
            cranelift_codegen::ir::BlockArg::Value(string),
        ],
    );

    builder.switch_to_block(write);
    let remaining = builder.block_params(write)[0];
    let position = builder.block_params(write)[1];
    let string = builder.block_params(write)[2];
    let ten = builder.ins().iconst(types::I64, 10);
    let digit = builder.ins().urem(remaining, ten);
    let digit = builder.ins().ireduce(types::I8, digit);
    let digit = builder.ins().iadd_imm(digit, i64::from(b'0'));
    let sign = builder.ins().uextend(types::I64, negative);
    let offset = builder.ins().iadd(position, sign);
    let offset = builder.ins().iadd_imm(offset, 7);
    let start = builder.ins().iadd_imm(string, 0);
    let address = builder.ins().iadd(start, offset);
    builder.ins().store(MemFlags::trusted(), digit, address, 0);
    let more = builder
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThan, position, 1);
    builder.ins().brif(
        more,
        write_more,
        &[
            cranelift_codegen::ir::BlockArg::Value(remaining),
            cranelift_codegen::ir::BlockArg::Value(position),
            cranelift_codegen::ir::BlockArg::Value(string),
        ],
        done,
        &[cranelift_codegen::ir::BlockArg::Value(string)],
    );

    builder.switch_to_block(write_more);
    let remaining = builder.block_params(write_more)[0];
    let position = builder.block_params(write_more)[1];
    let string = builder.block_params(write_more)[2];
    let ten = builder.ins().iconst(types::I64, 10);
    let remaining = builder.ins().udiv(remaining, ten);
    let position = builder.ins().iadd_imm(position, -1);
    builder.ins().jump(
        write,
        &[
            cranelift_codegen::ir::BlockArg::Value(remaining),
            cranelift_codegen::ir::BlockArg::Value(position),
            cranelift_codegen::ir::BlockArg::Value(string),
        ],
    );

    builder.switch_to_block(done);
    let string = builder.block_params(done)[0];
    builder.ins().return_(&[string]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

fn integer_width(
    builder: &mut FunctionBuilder<'_>,
    value: cranelift_codegen::ir::Value,
    wanted: types::Type,
) -> cranelift_codegen::ir::Value {
    let held = builder.func.dfg.value_type(value);
    match held.bits().cmp(&wanted.bits()) {
        std::cmp::Ordering::Greater => builder.ins().ireduce(wanted, value),
        std::cmp::Ordering::Less => builder.ins().uextend(wanted, value),
        std::cmp::Ordering::Equal => value,
    }
}

fn load_byte(
    builder: &mut FunctionBuilder<'_>,
    text: cranelift_codegen::ir::Value,
    index: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let start = builder.ins().iadd_imm(text, 8);
    let address = builder.ins().iadd(start, index);
    builder
        .ins()
        .load(types::I8, MemFlags::trusted(), address, 0)
}

fn copy_byte(
    builder: &mut FunctionBuilder<'_>,
    source: cranelift_codegen::ir::Value,
    source_index: cranelift_codegen::ir::Value,
    destination: cranelift_codegen::ir::Value,
    destination_index: cranelift_codegen::ir::Value,
) {
    let byte = load_byte(builder, source, source_index);
    let start = builder.ins().iadd_imm(destination, 8);
    let address = builder.ins().iadd(start, destination_index);
    builder.ins().store(MemFlags::trusted(), byte, address, 0);
}

fn define_abort(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
    exit: ModuleFuncId,
    write: ModuleFuncId,
    roots: DataId,
) -> Result<ModuleFuncId, Error> {
    let assertion_bytes = b"luar: trap: assertion-failed";
    let panic_bytes = b"luar: panic";
    let exception_bytes = b"luar: uncaught exception";
    let error_bytes = b"luar: error";
    let separator_bytes = b": ";
    let newline_bytes = b"\n";
    let trace_bytes = b"backtrace:\n";
    let frame_bytes = b"  at ";
    let assertion = static_data(module, "luar_assertion_prefix", assertion_bytes)?;
    let panic = static_data(module, "luar_panic_prefix", panic_bytes)?;
    let exception = static_data(module, "luar_exception_prefix", exception_bytes)?;
    let error = static_data(module, "luar_error_prefix", error_bytes)?;
    let separator = static_data(module, "luar_failure_separator", separator_bytes)?;
    let newline = static_data(module, "luar_failure_newline", newline_bytes)?;
    let trace = static_data(module, "luar_backtrace_header", trace_bytes)?;
    let frame_prefix = static_data(module, "luar_backtrace_frame", frame_bytes)?;

    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(types::I8));
    signature.params.push(AbiParam::new(pointer));
    signature.returns.push(AbiParam::new(types::I8));
    let declared = module
        .declare_function("luar_abort", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let assertion = module.declare_data_in_func(assertion, &mut context.func);
    let panic = module.declare_data_in_func(panic, &mut context.func);
    let exception = module.declare_data_in_func(exception, &mut context.func);
    let error = module.declare_data_in_func(error, &mut context.func);
    let separator = module.declare_data_in_func(separator, &mut context.func);
    let newline = module.declare_data_in_func(newline, &mut context.func);
    let trace = module.declare_data_in_func(trace, &mut context.func);
    let frame_prefix = module.declare_data_in_func(frame_prefix, &mut context.func);
    let roots = module.declare_data_in_func(roots, &mut context.func);
    let write = module.declare_func_in_func(write, &mut context.func);
    let exit = module.declare_func_in_func(exit, &mut context.func);

    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let panic_header = builder.create_block();
    let exception_header = builder.create_block();
    let assertion_header = builder.create_block();
    let error_header = builder.create_block();
    let after_header = builder.create_block();
    let message = builder.create_block();
    let trace_header = builder.create_block();
    let frames = builder.create_block();
    let write_frame = builder.create_block();
    let finish = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(frames, pointer);
    builder.append_block_param(write_frame, pointer);

    builder.switch_to_block(entry);
    let kind = builder.block_params(entry)[0];
    let value = builder.block_params(entry)[1];
    let choose = builder.create_block();
    let is_panic = builder.ins().icmp_imm(IntCC::Equal, kind, 1);
    builder.ins().brif(is_panic, panic_header, &[], choose, &[]);

    builder.switch_to_block(choose);
    let is_exception = builder.ins().icmp_imm(IntCC::Equal, kind, 2);
    let choose_error = builder.create_block();
    builder
        .ins()
        .brif(is_exception, exception_header, &[], choose_error, &[]);

    builder.switch_to_block(choose_error);
    let is_error = builder.ins().icmp_imm(IntCC::Equal, kind, 3);
    builder
        .ins()
        .brif(is_error, error_header, &[], assertion_header, &[]);

    builder.switch_to_block(panic_header);
    write_static(&mut builder, pointer, write, panic, panic_bytes.len());
    builder.ins().jump(after_header, &[]);

    // LR25.3: an exception escaping `main` reports the error and exits
    // unsuccessfully.
    builder.switch_to_block(exception_header);
    write_static(
        &mut builder,
        pointer,
        write,
        exception,
        exception_bytes.len(),
    );
    builder.ins().jump(after_header, &[]);

    builder.switch_to_block(error_header);
    write_static(&mut builder, pointer, write, error, error_bytes.len());
    builder.ins().jump(after_header, &[]);

    builder.switch_to_block(assertion_header);
    write_static(
        &mut builder,
        pointer,
        write,
        assertion,
        assertion_bytes.len(),
    );
    builder.ins().jump(after_header, &[]);

    builder.switch_to_block(after_header);
    let zero = builder.ins().iconst(pointer, 0);
    let present = builder.ins().icmp(IntCC::NotEqual, value, zero);
    builder.ins().brif(present, message, &[], trace_header, &[]);

    builder.switch_to_block(message);
    write_static(
        &mut builder,
        pointer,
        write,
        separator,
        separator_bytes.len(),
    );
    let length = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), value, 0);
    let length = builder.ins().ireduce(types::I32, length);
    let text = builder.ins().iadd_imm(value, 8);
    let stderr = builder.ins().iconst(types::I32, STDERR);
    builder.ins().call(write, &[stderr, text, length]);
    builder.ins().jump(trace_header, &[]);

    builder.switch_to_block(trace_header);
    write_static(&mut builder, pointer, write, newline, newline_bytes.len());
    write_static(&mut builder, pointer, write, trace, trace_bytes.len());
    let roots = builder.ins().global_value(pointer, roots);
    let first = builder.ins().load(pointer, MemFlags::trusted(), roots, 0);
    builder
        .ins()
        .jump(frames, &[cranelift_codegen::ir::BlockArg::Value(first)]);

    builder.switch_to_block(frames);
    let frame = builder.block_params(frames)[0];
    let zero = builder.ins().iconst(pointer, 0);
    let exhausted = builder.ins().icmp(IntCC::Equal, frame, zero);
    builder.ins().brif(
        exhausted,
        finish,
        &[],
        write_frame,
        &[cranelift_codegen::ir::BlockArg::Value(frame)],
    );

    builder.switch_to_block(write_frame);
    let frame = builder.block_params(write_frame)[0];
    write_static(
        &mut builder,
        pointer,
        write,
        frame_prefix,
        frame_bytes.len(),
    );
    let cell = i32::try_from(pointer.bytes()).expect("pointer width fits in i32");
    let name = builder
        .ins()
        .load(pointer, MemFlags::trusted(), frame, cell.saturating_mul(2));
    let name_length =
        builder
            .ins()
            .load(pointer, MemFlags::trusted(), frame, cell.saturating_mul(3));
    let name_length = if pointer.bits() > 32 {
        builder.ins().ireduce(types::I32, name_length)
    } else {
        name_length
    };
    let stderr = builder.ins().iconst(types::I32, STDERR);
    builder.ins().call(write, &[stderr, name, name_length]);
    write_static(&mut builder, pointer, write, newline, newline_bytes.len());
    let previous = builder.ins().load(pointer, MemFlags::trusted(), frame, 0);
    builder
        .ins()
        .jump(frames, &[cranelift_codegen::ir::BlockArg::Value(previous)]);

    builder.switch_to_block(finish);
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

fn static_data(module: &mut ObjectModule, name: &str, bytes: &[u8]) -> Result<DataId, Error> {
    let mut description = DataDescription::new();
    description.define(bytes.to_vec().into_boxed_slice());
    let data = module
        .declare_data(name, Linkage::Local, false, false)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    module
        .define_data(data, &description)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(data)
}

fn write_static(
    builder: &mut FunctionBuilder<'_>,
    pointer: types::Type,
    write: FuncRef,
    data: cranelift_codegen::ir::GlobalValue,
    length: usize,
) {
    let address = builder.ins().global_value(pointer, data);
    let length = builder
        .ins()
        .iconst(types::I32, i64::try_from(length).unwrap_or(0));
    let stderr = builder.ins().iconst(types::I32, STDERR);
    builder.ins().call(write, &[stderr, address, length]);
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

/// `luar_display_char`: a scalar value as the string of its UTF-8 encoding
/// (LR6.1, LR35).
fn define_display_char(
    module: &mut ObjectModule,
    pointer: types::Type,
    call_conv: CallConv,
    allocate: ModuleFuncId,
) -> Result<ModuleFuncId, Error> {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(types::I32));
    signature.returns.push(AbiParam::new(pointer));
    let declared = module
        .declare_function("luar_display_char", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let allocate = module.declare_func_in_func(allocate, &mut context.func);
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let not_four = builder.create_block();
    let not_three = builder.create_block();
    let blocks = [
        builder.create_block(),
        builder.create_block(),
        builder.create_block(),
        builder.create_block(),
    ];
    builder.append_block_params_for_function_params(entry);

    builder.switch_to_block(entry);
    let scalar = builder.block_params(entry)[0];
    let scalar = builder.ins().uextend(types::I64, scalar);
    let at_least_two = builder
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, scalar, 0x80);
    let at_least_three = builder
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, scalar, 0x800);
    let four = builder
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, scalar, 0x10000);
    let mut length = builder.ins().iconst(types::I64, 1);
    for more in [at_least_two, at_least_three, four] {
        let more = builder.ins().uextend(types::I64, more);
        length = builder.ins().iadd(length, more);
    }
    // The length cell, and one cell holding at most four bytes.
    let bytes = builder.ins().iconst(types::I64, 16);
    let bytes = integer_width(&mut builder, bytes, pointer);
    let no_finalizer = builder.ins().iconst(pointer, 0);
    let call = builder.ins().call(allocate, &[bytes, no_finalizer]);
    let string = builder.inst_results(call)[0];
    builder.ins().store(MemFlags::trusted(), length, string, 0);
    builder.ins().brif(four, blocks[3], &[], not_four, &[]);

    builder.switch_to_block(not_four);
    builder
        .ins()
        .brif(at_least_three, blocks[2], &[], not_three, &[]);

    builder.switch_to_block(not_three);
    builder
        .ins()
        .brif(at_least_two, blocks[1], &[], blocks[0], &[]);

    // One byte for each block, with the lead byte marking how many follow.
    for (index, block) in blocks.into_iter().enumerate() {
        builder.switch_to_block(block);
        let count = index + 1;
        let lead = match count {
            1 => 0x00,
            2 => 0xC0,
            3 => 0xE0,
            _ => 0xF0,
        };
        for position in 0..count {
            let shift = i64::try_from(6 * (count - 1 - position)).expect("shift fits");
            let part = builder.ins().ushr_imm(scalar, shift);
            let (mask, marker) = if position == 0 {
                (
                    if count == 1 {
                        0x7F
                    } else {
                        0xFF >> (count + 1)
                    },
                    lead,
                )
            } else {
                (0x3F, 0x80)
            };
            let part = builder.ins().band_imm(part, mask);
            let part = builder.ins().bor_imm(part, marker);
            let byte = builder.ins().ireduce(types::I8, part);
            let offset = 8 + i32::try_from(position).expect("offset fits");
            builder
                .ins()
                .store(MemFlags::trusted(), byte, string, offset);
        }
        builder.ins().return_(&[string]);
    }

    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}
