use cranelift_codegen::Context;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, Signature, Type, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use cranelift_object::ObjectModule;

use crate::Error;

const OWNED: MemFlags = MemFlags::trusted();
const INITIAL_CAPACITY: i64 = 4096;
const RESULT_BYTES: i64 = 16;
const STRING_HEADER_BYTES: i64 = 8;

pub(crate) fn emit(
    module: &mut ObjectModule,
    pointer: Type,
    call_conv: CallConv,
    allocate: FuncId,
) -> Result<FuncId, Error> {
    let valid_utf8 = define_valid_utf8(module, pointer, call_conv)?;
    define_read_text(module, pointer, call_conv, allocate, valid_utf8)
}

fn define_valid_utf8(
    module: &mut ObjectModule,
    pointer: Type,
    call_conv: CallConv,
) -> Result<FuncId, Error> {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(types::I64));
    signature.returns.push(AbiParam::new(types::I8));
    let declared = module
        .declare_function("luar_valid_utf8", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let inspect = builder.create_block();
    let classify_two = builder.create_block();
    let classify_three = builder.create_block();
    let classify_four = builder.create_block();
    let check_two = builder.create_block();
    let check_three = builder.create_block();
    let check_four = builder.create_block();
    let valid = builder.create_block();
    let invalid = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(inspect, types::I64);

    builder.switch_to_block(entry);
    let bytes = builder.block_params(entry)[0];
    let length = builder.block_params(entry)[1];
    let zero = builder.ins().iconst(types::I64, 0);
    builder
        .ins()
        .jump(inspect, &[cranelift_codegen::ir::BlockArg::Value(zero)]);

    builder.switch_to_block(inspect);
    let index = builder.block_params(inspect)[0];
    let done = builder
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, index, length);
    let classify = builder.create_block();
    builder.ins().brif(done, valid, &[], classify, &[]);

    builder.switch_to_block(classify);
    let byte = load_byte(&mut builder, bytes, index, pointer);
    let ascii = builder.ins().icmp_imm(IntCC::UnsignedLessThan, byte, 0x80);
    let next = builder.ins().iadd_imm(index, 1);
    builder.ins().brif(
        ascii,
        inspect,
        &[cranelift_codegen::ir::BlockArg::Value(next)],
        classify_two,
        &[],
    );

    builder.switch_to_block(classify_two);
    let two = between(&mut builder, byte, 0xc2, 0xdf);
    builder.ins().brif(two, check_two, &[], classify_three, &[]);

    builder.switch_to_block(classify_three);
    let three = between(&mut builder, byte, 0xe0, 0xef);
    builder
        .ins()
        .brif(three, check_three, &[], classify_four, &[]);

    builder.switch_to_block(classify_four);
    let four = between(&mut builder, byte, 0xf0, 0xf4);
    builder.ins().brif(four, check_four, &[], invalid, &[]);

    builder.switch_to_block(check_two);
    let last = builder.ins().iadd_imm(index, 1);
    let present = builder.ins().icmp(IntCC::UnsignedLessThan, last, length);
    let inspect_two = builder.create_block();
    builder.ins().brif(present, inspect_two, &[], invalid, &[]);

    builder.switch_to_block(inspect_two);
    let second = load_byte(&mut builder, bytes, last, pointer);
    let continuation = between(&mut builder, second, 0x80, 0xbf);
    let next = builder.ins().iadd_imm(index, 2);
    builder.ins().brif(
        continuation,
        inspect,
        &[cranelift_codegen::ir::BlockArg::Value(next)],
        invalid,
        &[],
    );

    builder.switch_to_block(check_three);
    let last = builder.ins().iadd_imm(index, 2);
    let present = builder.ins().icmp(IntCC::UnsignedLessThan, last, length);
    let inspect_three = builder.create_block();
    builder
        .ins()
        .brif(present, inspect_three, &[], invalid, &[]);

    builder.switch_to_block(inspect_three);
    let second_index = builder.ins().iadd_imm(index, 1);
    let second = load_byte(&mut builder, bytes, second_index, pointer);
    let third = load_byte(&mut builder, bytes, last, pointer);
    let second_continues = between(&mut builder, second, 0x80, 0xbf);
    let third_continues = between(&mut builder, third, 0x80, 0xbf);
    let continuations = builder.ins().band(second_continues, third_continues);
    let lead = builder.ins().uextend(types::I32, byte);
    let second = builder.ins().uextend(types::I32, second);
    let third = builder.ins().uextend(types::I32, third);
    let lead = builder.ins().band_imm(lead, 0x0f);
    let second = builder.ins().band_imm(second, 0x3f);
    let third = builder.ins().band_imm(third, 0x3f);
    let lead = builder.ins().ishl_imm(lead, 12);
    let second = builder.ins().ishl_imm(second, 6);
    let prefix = builder.ins().bor(lead, second);
    let scalar = builder.ins().bor(prefix, third);
    let long_enough = builder
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, scalar, 0x800);
    let below_surrogates = builder
        .ins()
        .icmp_imm(IntCC::UnsignedLessThan, scalar, 0xd800);
    let above_surrogates = builder
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThan, scalar, 0xdfff);
    let not_surrogate = builder.ins().bor(below_surrogates, above_surrogates);
    let valid_scalar = builder.ins().band(long_enough, not_surrogate);
    let scalar = builder.ins().band(continuations, valid_scalar);
    let next = builder.ins().iadd_imm(index, 3);
    builder.ins().brif(
        scalar,
        inspect,
        &[cranelift_codegen::ir::BlockArg::Value(next)],
        invalid,
        &[],
    );

    builder.switch_to_block(check_four);
    let last = builder.ins().iadd_imm(index, 3);
    let present = builder.ins().icmp(IntCC::UnsignedLessThan, last, length);
    let inspect_four = builder.create_block();
    builder.ins().brif(present, inspect_four, &[], invalid, &[]);

    builder.switch_to_block(inspect_four);
    let second_index = builder.ins().iadd_imm(index, 1);
    let third_index = builder.ins().iadd_imm(index, 2);
    let second = load_byte(&mut builder, bytes, second_index, pointer);
    let third = load_byte(&mut builder, bytes, third_index, pointer);
    let fourth = load_byte(&mut builder, bytes, last, pointer);
    let second_continues = between(&mut builder, second, 0x80, 0xbf);
    let third_continues = between(&mut builder, third, 0x80, 0xbf);
    let fourth_continues = between(&mut builder, fourth, 0x80, 0xbf);
    let later_continue = builder.ins().band(third_continues, fourth_continues);
    let continuations = builder.ins().band(second_continues, later_continue);
    let lead = builder.ins().uextend(types::I32, byte);
    let second = builder.ins().uextend(types::I32, second);
    let third = builder.ins().uextend(types::I32, third);
    let fourth = builder.ins().uextend(types::I32, fourth);
    let lead = builder.ins().band_imm(lead, 0x07);
    let second = builder.ins().band_imm(second, 0x3f);
    let third = builder.ins().band_imm(third, 0x3f);
    let fourth = builder.ins().band_imm(fourth, 0x3f);
    let lead = builder.ins().ishl_imm(lead, 18);
    let second = builder.ins().ishl_imm(second, 12);
    let third = builder.ins().ishl_imm(third, 6);
    let prefix = builder.ins().bor(lead, second);
    let suffix = builder.ins().bor(third, fourth);
    let scalar = builder.ins().bor(prefix, suffix);
    let long_enough = builder
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, scalar, 0x10000);
    let in_range = builder
        .ins()
        .icmp_imm(IntCC::UnsignedLessThanOrEqual, scalar, 0x10ffff);
    let valid_scalar = builder.ins().band(long_enough, in_range);
    let scalar = builder.ins().band(continuations, valid_scalar);
    let next = builder.ins().iadd_imm(index, 4);
    builder.ins().brif(
        scalar,
        inspect,
        &[cranelift_codegen::ir::BlockArg::Value(next)],
        invalid,
        &[],
    );

    builder.switch_to_block(valid);
    let one = builder.ins().iconst(types::I8, 1);
    builder.ins().return_(&[one]);

    builder.switch_to_block(invalid);
    let zero = builder.ins().iconst(types::I8, 0);
    builder.ins().return_(&[zero]);

    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

fn define_read_text(
    module: &mut ObjectModule,
    pointer: Type,
    call_conv: CallConv,
    allocate: FuncId,
    valid_utf8: FuncId,
) -> Result<FuncId, Error> {
    let mode = static_data(module, "luar_read_text_mode", b"rb\0")?;
    let message = b"could not read file";
    let mut error = i64::try_from(message.len())
        .unwrap_or(0)
        .to_le_bytes()
        .to_vec();
    error.extend_from_slice(message);
    let error = static_data(module, "luar_read_text_error", &error)?;

    let mut malloc_signature = Signature::new(call_conv);
    malloc_signature.params.push(AbiParam::new(pointer));
    malloc_signature.returns.push(AbiParam::new(pointer));
    let malloc = module
        .declare_function("malloc", Linkage::Import, &malloc_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut realloc_signature = Signature::new(call_conv);
    realloc_signature.params.push(AbiParam::new(pointer));
    realloc_signature.params.push(AbiParam::new(pointer));
    realloc_signature.returns.push(AbiParam::new(pointer));
    let realloc = module
        .declare_function("realloc", Linkage::Import, &realloc_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut free_signature = Signature::new(call_conv);
    free_signature.params.push(AbiParam::new(pointer));
    let free = module
        .declare_function("free", Linkage::Import, &free_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut fopen_signature = Signature::new(call_conv);
    fopen_signature.params.push(AbiParam::new(pointer));
    fopen_signature.params.push(AbiParam::new(pointer));
    fopen_signature.returns.push(AbiParam::new(pointer));
    let fopen = module
        .declare_function("fopen", Linkage::Import, &fopen_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut file_int_signature = Signature::new(call_conv);
    file_int_signature.params.push(AbiParam::new(pointer));
    file_int_signature.returns.push(AbiParam::new(types::I32));
    let fgetc = module
        .declare_function("fgetc", Linkage::Import, &file_int_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    let ferror = module
        .declare_function("ferror", Linkage::Import, &file_int_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    let fclose = module
        .declare_function("fclose", Linkage::Import, &file_int_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(pointer));
    signature.returns.push(AbiParam::new(pointer));
    let declared = module
        .declare_function("luar_read_text", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let allocate = module.declare_func_in_func(allocate, &mut context.func);
    let valid_utf8 = module.declare_func_in_func(valid_utf8, &mut context.func);
    let malloc = module.declare_func_in_func(malloc, &mut context.func);
    let realloc = module.declare_func_in_func(realloc, &mut context.func);
    let free = module.declare_func_in_func(free, &mut context.func);
    let fopen = module.declare_func_in_func(fopen, &mut context.func);
    let fgetc = module.declare_func_in_func(fgetc, &mut context.func);
    let ferror = module.declare_func_in_func(ferror, &mut context.func);
    let fclose = module.declare_func_in_func(fclose, &mut context.func);
    let mode = module.declare_data_in_func(mode, &mut context.func);
    let error = module.declare_data_in_func(error, &mut context.func);

    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let copy_path = builder.create_block();
    let copy_path_byte = builder.create_block();
    let open_file = builder.create_block();
    let opened = builder.create_block();
    let read = builder.create_block();
    let have_byte = builder.create_block();
    let grow = builder.create_block();
    let store_byte = builder.create_block();
    let eof = builder.create_block();
    let check_text = builder.create_block();
    let success = builder.create_block();
    let copy_text = builder.create_block();
    let copy_text_byte = builder.create_block();
    let success_done = builder.create_block();
    let fail = builder.create_block();
    let fail_path = builder.create_block();
    let fail_file = builder.create_block();
    let fail_buffer = builder.create_block();
    let fail_closed_buffer = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(copy_path, types::I64);
    builder.append_block_param(copy_path_byte, types::I64);
    for block in [read, eof, check_text, success] {
        builder.append_block_param(block, pointer);
        builder.append_block_param(block, types::I64);
    }
    builder.append_block_param(read, types::I64);
    for block in [have_byte, grow, store_byte] {
        builder.append_block_param(block, pointer);
        builder.append_block_param(block, types::I64);
        builder.append_block_param(block, types::I64);
        builder.append_block_param(block, types::I8);
    }
    for block in [copy_text, copy_text_byte] {
        builder.append_block_param(block, pointer);
        builder.append_block_param(block, types::I64);
        builder.append_block_param(block, pointer);
        builder.append_block_param(block, types::I64);
    }
    builder.append_block_param(success_done, pointer);
    builder.append_block_param(success_done, pointer);
    builder.append_block_param(fail_buffer, pointer);
    builder.append_block_param(fail_closed_buffer, pointer);

    builder.switch_to_block(entry);
    let path = builder.block_params(entry)[0];
    let path_length = builder.ins().load(types::I64, OWNED, path, 0);
    let c_path_bytes = builder.ins().iadd_imm(path_length, 1);
    let c_path_bytes = integer_width(&mut builder, c_path_bytes, pointer);
    let call = builder.ins().call(malloc, &[c_path_bytes]);
    let c_path = builder.inst_results(call)[0];
    let zero_pointer = builder.ins().iconst(pointer, 0);
    let unavailable = builder.ins().icmp(IntCC::Equal, c_path, zero_pointer);
    let zero = builder.ins().iconst(types::I64, 0);
    builder.ins().brif(
        unavailable,
        fail,
        &[],
        copy_path,
        &[cranelift_codegen::ir::BlockArg::Value(zero)],
    );

    builder.switch_to_block(copy_path);
    let index = builder.block_params(copy_path)[0];
    let done = builder
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, index, path_length);
    builder.ins().brif(
        done,
        open_file,
        &[],
        copy_path_byte,
        &[cranelift_codegen::ir::BlockArg::Value(index)],
    );

    builder.switch_to_block(copy_path_byte);
    let index = builder.block_params(copy_path_byte)[0];
    let byte = load_string_byte(&mut builder, path, index, pointer);
    let nul = builder.ins().icmp_imm(IntCC::Equal, byte, 0);
    let write_path = builder.create_block();
    builder.ins().brif(nul, fail_path, &[], write_path, &[]);

    builder.switch_to_block(write_path);
    let address = address_at(&mut builder, c_path, index, pointer);
    builder.ins().store(OWNED, byte, address, 0);
    let next = builder.ins().iadd_imm(index, 1);
    builder
        .ins()
        .jump(copy_path, &[cranelift_codegen::ir::BlockArg::Value(next)]);

    builder.switch_to_block(open_file);
    let end = address_at(&mut builder, c_path, path_length, pointer);
    let nul = builder.ins().iconst(types::I8, 0);
    builder.ins().store(OWNED, nul, end, 0);
    let mode = builder.ins().global_value(pointer, mode);
    let call = builder.ins().call(fopen, &[c_path, mode]);
    let file = builder.inst_results(call)[0];
    builder.ins().call(free, &[c_path]);
    let zero = builder.ins().iconst(pointer, 0);
    let unavailable = builder.ins().icmp(IntCC::Equal, file, zero);
    builder.ins().brif(unavailable, fail, &[], opened, &[]);

    builder.switch_to_block(opened);
    let capacity = builder.ins().iconst(types::I64, INITIAL_CAPACITY);
    let allocation = integer_width(&mut builder, capacity, pointer);
    let call = builder.ins().call(malloc, &[allocation]);
    let buffer = builder.inst_results(call)[0];
    let zero_pointer = builder.ins().iconst(pointer, 0);
    let unavailable = builder.ins().icmp(IntCC::Equal, buffer, zero_pointer);
    let zero = builder.ins().iconst(types::I64, 0);
    builder.ins().brif(
        unavailable,
        fail_file,
        &[],
        read,
        &[
            cranelift_codegen::ir::BlockArg::Value(buffer),
            cranelift_codegen::ir::BlockArg::Value(zero),
            cranelift_codegen::ir::BlockArg::Value(capacity),
        ],
    );

    builder.switch_to_block(read);
    let buffer = builder.block_params(read)[0];
    let length = builder.block_params(read)[1];
    let capacity = builder.block_params(read)[2];
    let call = builder.ins().call(fgetc, &[file]);
    let read_byte = builder.inst_results(call)[0];
    let exhausted = builder.ins().icmp_imm(IntCC::Equal, read_byte, -1);
    let byte = builder.ins().ireduce(types::I8, read_byte);
    builder.ins().brif(
        exhausted,
        eof,
        &[
            cranelift_codegen::ir::BlockArg::Value(buffer),
            cranelift_codegen::ir::BlockArg::Value(length),
        ],
        have_byte,
        &[
            cranelift_codegen::ir::BlockArg::Value(buffer),
            cranelift_codegen::ir::BlockArg::Value(length),
            cranelift_codegen::ir::BlockArg::Value(capacity),
            cranelift_codegen::ir::BlockArg::Value(byte),
        ],
    );

    builder.switch_to_block(have_byte);
    let buffer = builder.block_params(have_byte)[0];
    let length = builder.block_params(have_byte)[1];
    let capacity = builder.block_params(have_byte)[2];
    let byte = builder.block_params(have_byte)[3];
    let full = builder.ins().icmp(IntCC::Equal, length, capacity);
    let args = [
        cranelift_codegen::ir::BlockArg::Value(buffer),
        cranelift_codegen::ir::BlockArg::Value(length),
        cranelift_codegen::ir::BlockArg::Value(capacity),
        cranelift_codegen::ir::BlockArg::Value(byte),
    ];
    builder.ins().brif(full, grow, &args, store_byte, &args);

    builder.switch_to_block(grow);
    let buffer = builder.block_params(grow)[0];
    let length = builder.block_params(grow)[1];
    let capacity = builder.block_params(grow)[2];
    let byte = builder.block_params(grow)[3];
    let capacity = builder.ins().imul_imm(capacity, 2);
    let allocation = integer_width(&mut builder, capacity, pointer);
    let call = builder.ins().call(realloc, &[buffer, allocation]);
    let grown = builder.inst_results(call)[0];
    let zero = builder.ins().iconst(pointer, 0);
    let unavailable = builder.ins().icmp(IntCC::Equal, grown, zero);
    builder.ins().brif(
        unavailable,
        fail_buffer,
        &[cranelift_codegen::ir::BlockArg::Value(buffer)],
        store_byte,
        &[
            cranelift_codegen::ir::BlockArg::Value(grown),
            cranelift_codegen::ir::BlockArg::Value(length),
            cranelift_codegen::ir::BlockArg::Value(capacity),
            cranelift_codegen::ir::BlockArg::Value(byte),
        ],
    );

    builder.switch_to_block(store_byte);
    let buffer = builder.block_params(store_byte)[0];
    let length = builder.block_params(store_byte)[1];
    let capacity = builder.block_params(store_byte)[2];
    let byte = builder.block_params(store_byte)[3];
    let address = address_at(&mut builder, buffer, length, pointer);
    builder.ins().store(OWNED, byte, address, 0);
    let length = builder.ins().iadd_imm(length, 1);
    builder.ins().jump(
        read,
        &[
            cranelift_codegen::ir::BlockArg::Value(buffer),
            cranelift_codegen::ir::BlockArg::Value(length),
            cranelift_codegen::ir::BlockArg::Value(capacity),
        ],
    );

    builder.switch_to_block(eof);
    let buffer = builder.block_params(eof)[0];
    let length = builder.block_params(eof)[1];
    let call = builder.ins().call(ferror, &[file]);
    let errored = builder.inst_results(call)[0];
    builder.ins().call(fclose, &[file]);
    let errored = builder.ins().icmp_imm(IntCC::NotEqual, errored, 0);
    builder.ins().brif(
        errored,
        fail_closed_buffer,
        &[cranelift_codegen::ir::BlockArg::Value(buffer)],
        check_text,
        &[
            cranelift_codegen::ir::BlockArg::Value(buffer),
            cranelift_codegen::ir::BlockArg::Value(length),
        ],
    );

    builder.switch_to_block(check_text);
    let buffer = builder.block_params(check_text)[0];
    let length = builder.block_params(check_text)[1];
    let call = builder.ins().call(valid_utf8, &[buffer, length]);
    let valid = builder.inst_results(call)[0];
    builder.ins().brif(
        valid,
        success,
        &[
            cranelift_codegen::ir::BlockArg::Value(buffer),
            cranelift_codegen::ir::BlockArg::Value(length),
        ],
        fail_closed_buffer,
        &[cranelift_codegen::ir::BlockArg::Value(buffer)],
    );

    builder.switch_to_block(success);
    let buffer = builder.block_params(success)[0];
    let length = builder.block_params(success)[1];
    let cell = i64::from(pointer.bytes());
    let allocation = builder
        .ins()
        .iadd_imm(length, RESULT_BYTES + STRING_HEADER_BYTES + cell - 1);
    let allocation = builder.ins().band_imm(allocation, -cell);
    let allocation = integer_width(&mut builder, allocation, pointer);
    let no_finalizer = builder.ins().iconst(pointer, 0);
    let call = builder.ins().call(allocate, &[allocation, no_finalizer]);
    let result = builder.inst_results(call)[0];
    let tag = builder.ins().iconst(types::I64, 0);
    builder.ins().store(OWNED, tag, result, 0);
    let string = builder.ins().iadd_imm(result, RESULT_BYTES);
    builder.ins().store(OWNED, string, result, 8);
    builder.ins().store(OWNED, length, string, 0);
    let zero = builder.ins().iconst(types::I64, 0);
    builder.ins().jump(
        copy_text,
        &[
            cranelift_codegen::ir::BlockArg::Value(buffer),
            cranelift_codegen::ir::BlockArg::Value(length),
            cranelift_codegen::ir::BlockArg::Value(result),
            cranelift_codegen::ir::BlockArg::Value(zero),
        ],
    );

    builder.switch_to_block(copy_text);
    let buffer = builder.block_params(copy_text)[0];
    let length = builder.block_params(copy_text)[1];
    let result = builder.block_params(copy_text)[2];
    let index = builder.block_params(copy_text)[3];
    let done = builder
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, index, length);
    builder.ins().brif(
        done,
        success_done,
        &[
            cranelift_codegen::ir::BlockArg::Value(buffer),
            cranelift_codegen::ir::BlockArg::Value(result),
        ],
        copy_text_byte,
        &[
            cranelift_codegen::ir::BlockArg::Value(buffer),
            cranelift_codegen::ir::BlockArg::Value(length),
            cranelift_codegen::ir::BlockArg::Value(result),
            cranelift_codegen::ir::BlockArg::Value(index),
        ],
    );

    builder.switch_to_block(copy_text_byte);
    let buffer = builder.block_params(copy_text_byte)[0];
    let length = builder.block_params(copy_text_byte)[1];
    let result = builder.block_params(copy_text_byte)[2];
    let index = builder.block_params(copy_text_byte)[3];
    let source = address_at(&mut builder, buffer, index, pointer);
    let byte = builder.ins().load(types::I8, OWNED, source, 0);
    let string = builder.ins().iadd_imm(result, RESULT_BYTES);
    let start = builder.ins().iadd_imm(string, STRING_HEADER_BYTES);
    let target = address_at(&mut builder, start, index, pointer);
    builder.ins().store(OWNED, byte, target, 0);
    let index = builder.ins().iadd_imm(index, 1);
    builder.ins().jump(
        copy_text,
        &[
            cranelift_codegen::ir::BlockArg::Value(buffer),
            cranelift_codegen::ir::BlockArg::Value(length),
            cranelift_codegen::ir::BlockArg::Value(result),
            cranelift_codegen::ir::BlockArg::Value(index),
        ],
    );

    builder.switch_to_block(success_done);
    let buffer = builder.block_params(success_done)[0];
    let result = builder.block_params(success_done)[1];
    builder.ins().call(free, &[buffer]);
    builder.ins().return_(&[result]);

    builder.switch_to_block(fail_path);
    builder.ins().call(free, &[c_path]);
    builder.ins().jump(fail, &[]);

    builder.switch_to_block(fail_file);
    builder.ins().call(fclose, &[file]);
    builder.ins().jump(fail, &[]);

    builder.switch_to_block(fail_buffer);
    let buffer = builder.block_params(fail_buffer)[0];
    builder.ins().call(free, &[buffer]);
    builder.ins().call(fclose, &[file]);
    builder.ins().jump(fail, &[]);

    builder.switch_to_block(fail_closed_buffer);
    let buffer = builder.block_params(fail_closed_buffer)[0];
    builder.ins().call(free, &[buffer]);
    builder.ins().jump(fail, &[]);

    builder.switch_to_block(fail);
    let bytes = builder.ins().iconst(pointer, RESULT_BYTES);
    let no_finalizer = builder.ins().iconst(pointer, 0);
    let call = builder.ins().call(allocate, &[bytes, no_finalizer]);
    let result = builder.inst_results(call)[0];
    let tag = builder.ins().iconst(types::I64, 1);
    builder.ins().store(OWNED, tag, result, 0);
    let error = builder.ins().global_value(pointer, error);
    builder.ins().store(OWNED, error, result, 8);
    builder.ins().return_(&[result]);

    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

fn between(
    builder: &mut FunctionBuilder<'_>,
    value: cranelift_codegen::ir::Value,
    lower: i64,
    upper: i64,
) -> cranelift_codegen::ir::Value {
    let at_least = builder
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, value, lower);
    let at_most = builder
        .ins()
        .icmp_imm(IntCC::UnsignedLessThanOrEqual, value, upper);
    builder.ins().band(at_least, at_most)
}

fn load_byte(
    builder: &mut FunctionBuilder<'_>,
    bytes: cranelift_codegen::ir::Value,
    index: cranelift_codegen::ir::Value,
    pointer: Type,
) -> cranelift_codegen::ir::Value {
    let address = address_at(builder, bytes, index, pointer);
    builder.ins().load(types::I8, OWNED, address, 0)
}

fn load_string_byte(
    builder: &mut FunctionBuilder<'_>,
    string: cranelift_codegen::ir::Value,
    index: cranelift_codegen::ir::Value,
    pointer: Type,
) -> cranelift_codegen::ir::Value {
    let bytes = builder.ins().iadd_imm(string, STRING_HEADER_BYTES);
    load_byte(builder, bytes, index, pointer)
}

fn address_at(
    builder: &mut FunctionBuilder<'_>,
    base: cranelift_codegen::ir::Value,
    offset: cranelift_codegen::ir::Value,
    pointer: Type,
) -> cranelift_codegen::ir::Value {
    let offset = integer_width(builder, offset, pointer);
    builder.ins().iadd(base, offset)
}

fn integer_width(
    builder: &mut FunctionBuilder<'_>,
    value: cranelift_codegen::ir::Value,
    wanted: Type,
) -> cranelift_codegen::ir::Value {
    let held = builder.func.dfg.value_type(value);
    match held.bits().cmp(&wanted.bits()) {
        std::cmp::Ordering::Greater => builder.ins().ireduce(wanted, value),
        std::cmp::Ordering::Less => builder.ins().uextend(wanted, value),
        std::cmp::Ordering::Equal => value,
    }
}

fn static_data(
    module: &mut ObjectModule,
    name: &str,
    bytes: &[u8],
) -> Result<cranelift_module::DataId, Error> {
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
