//! The handful of functions the emitted program needs at runtime.
//!
//! They are emitted into the same object rather than shipped as a library, so
//! a build needs a linker and a C runtime and nothing else.

use cranelift_codegen::Context;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{AbiParam, FuncRef, InstBuilder, MemFlags, Signature, TrapCode, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId as ModuleFuncId, Linkage, Module};
use cranelift_object::ObjectModule;
use luar_lir::inst::Trap;

use crate::Error;
use crate::fs;
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

/// What the emitted program reaches at runtime.
pub(crate) struct Runtime {
    /// One handler per trap kind, in [`TRAPS`] order.
    pub handlers: [ModuleFuncId; TRAPS.len()],
    /// Where managed aggregate storage comes from (LR29).
    pub allocate: ModuleFuncId,
    /// Primitive string operations (LR11.2, LR11.3, LR35).
    pub concat: ModuleFuncId,
    pub text_equal: ModuleFuncId,
    pub hash_bytes: ModuleFuncId,
    pub display_signed: ModuleFuncId,
    pub display_unsigned: ModuleFuncId,
    pub print: ModuleFuncId,
    pub read_text: ModuleFuncId,
    pub abort: ModuleFuncId,
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
        let concat = define_concat(module, pointer, call_conv, collector.allocate)?;
        let text_equal = define_text_equal(module, pointer, call_conv)?;
        let hash_bytes = define_hash_bytes(module, pointer, call_conv)?;
        let display_signed =
            define_display_integer(module, pointer, call_conv, collector.allocate, true)?;
        let display_unsigned =
            define_display_integer(module, pointer, call_conv, collector.allocate, false)?;
        let print = define_print(module, pointer, call_conv, write)?;
        let read_text = fs::emit(module, pointer, call_conv, collector.allocate)?;
        let abort = define_abort(module, pointer, call_conv, exit, write, collector.roots)?;
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
            concat,
            text_equal,
            hash_bytes,
            display_signed,
            display_unsigned,
            print,
            read_text,
            abort,
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

    pub fn display_unsigned_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.display_unsigned, function)
    }

    pub fn print_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.print, function)
    }

    pub fn read_text_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.read_text, function)
    }

    pub fn abort_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> FuncRef {
        module.declare_func_in_func(self.abort, function)
    }

    pub fn roots_in(
        &self,
        module: &mut ObjectModule,
        function: &mut cranelift_codegen::ir::Function,
    ) -> cranelift_codegen::ir::GlobalValue {
        module.declare_data_in_func(self.roots, function)
    }
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
