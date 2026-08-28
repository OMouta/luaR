use cranelift_codegen::Context;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, Signature, Type, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use cranelift_object::ObjectModule;

use crate::Error;

const COLLECT_AFTER: i64 = 1024 * 1024;
const OWNED: MemFlags = MemFlags::trusted();

/// Previous frame, root count, function name, and function-name length.
pub(crate) const ROOT_FRAME_HEADER: i32 = 4;

pub(crate) struct Collector {
    pub allocate: FuncId,
    pub roots: DataId,
}

pub(crate) fn emit(
    module: &mut ObjectModule,
    pointer: Type,
    call_conv: CallConv,
) -> Result<Collector, Error> {
    let roots = zero(module, "luar_gc_roots", pointer)?;
    let head = zero(module, "luar_gc_head", pointer)?;
    let allocated = zero(module, "luar_gc_allocated", pointer)?;
    let collecting = zero(module, "luar_gc_collecting", pointer)?;

    let mut malloc_signature = Signature::new(call_conv);
    malloc_signature.params.push(AbiParam::new(pointer));
    malloc_signature.returns.push(AbiParam::new(pointer));
    let malloc = module
        .declare_function("malloc", Linkage::Import, &malloc_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut free_signature = Signature::new(call_conv);
    free_signature.params.push(AbiParam::new(pointer));
    let free = module
        .declare_function("free", Linkage::Import, &free_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut mark_signature = Signature::new(call_conv);
    mark_signature.params.push(AbiParam::new(pointer));
    let mark = module
        .declare_function("luar_gc_mark", Linkage::Local, &mark_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let collect_signature = Signature::new(call_conv);
    let mark_roots = module
        .declare_function("luar_gc_mark_roots", Linkage::Local, &collect_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    let finalize = module
        .declare_function("luar_gc_finalize", Linkage::Local, &collect_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    let collect = module
        .declare_function("luar_gc_collect", Linkage::Local, &collect_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut allocate_signature = malloc_signature.clone();
    allocate_signature.params.push(AbiParam::new(pointer));
    let allocate = module
        .declare_function("luar_gc_allocate", Linkage::Local, &allocate_signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    define_mark(module, pointer, mark, mark_signature, head)?;
    define_mark_roots(
        module,
        pointer,
        mark_roots,
        collect_signature.clone(),
        roots,
        mark,
    )?;
    define_finalize(
        module,
        pointer,
        call_conv,
        finalize,
        collect_signature.clone(),
        head,
        mark,
    )?;
    define_collect(
        module,
        pointer,
        collect,
        collect_signature,
        head,
        allocated,
        collecting,
        mark_roots,
        finalize,
        free,
    )?;
    define_allocate(
        module,
        pointer,
        allocate,
        allocate_signature,
        head,
        allocated,
        collecting,
        collect,
        malloc,
    )?;

    Ok(Collector { allocate, roots })
}

fn zero(module: &mut ObjectModule, name: &str, pointer: Type) -> Result<DataId, Error> {
    let mut description = DataDescription::new();
    description.define_zeroinit(pointer.bytes() as usize);
    let data = module
        .declare_data(name, Linkage::Local, true, false)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    module
        .define_data(data, &description)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(data)
}

fn define_mark(
    module: &mut ObjectModule,
    pointer: Type,
    declared: FuncId,
    signature: Signature,
    head: DataId,
) -> Result<(), Error> {
    let cell = i64::from(pointer.bytes());
    let size_offset = i32::try_from(cell).expect("pointer width fits in i32");
    let mark_offset = size_offset * 2;
    let payload_offset = cell * 4;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let head = module.declare_data_in_func(head, &mut context.func);
    let recursive = module.declare_func_in_func(declared, &mut context.func);

    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let search = builder.create_block();
    let inspect = builder.create_block();
    let found = builder.create_block();
    let scan = builder.create_block();
    let scan_one = builder.create_block();
    let done = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(search, pointer);
    builder.append_block_param(inspect, pointer);
    builder.append_block_param(found, pointer);
    builder.append_block_param(scan, pointer);
    builder.append_block_param(scan, pointer);
    builder.append_block_param(scan, pointer);

    builder.switch_to_block(entry);
    let candidate = builder.block_params(entry)[0];
    let zero = builder.ins().iconst(pointer, 0);
    let absent = builder.ins().icmp(IntCC::Equal, candidate, zero);
    let head_address = builder.ins().global_value(pointer, head);
    let first = builder.ins().load(pointer, OWNED, head_address, 0);
    builder.ins().brif(
        absent,
        done,
        &[],
        search,
        &[cranelift_codegen::ir::BlockArg::Value(first)],
    );

    builder.switch_to_block(search);
    let header = builder.block_params(search)[0];
    let zero = builder.ins().iconst(pointer, 0);
    let exhausted = builder.ins().icmp(IntCC::Equal, header, zero);
    builder.ins().brif(
        exhausted,
        done,
        &[],
        inspect,
        &[cranelift_codegen::ir::BlockArg::Value(header)],
    );

    builder.switch_to_block(inspect);
    let header = builder.block_params(inspect)[0];
    let payload = builder.ins().iadd_imm(header, payload_offset);
    let matches = builder.ins().icmp(IntCC::Equal, candidate, payload);
    let next = builder.ins().load(pointer, OWNED, header, 0);
    builder.ins().brif(
        matches,
        found,
        &[cranelift_codegen::ir::BlockArg::Value(header)],
        search,
        &[cranelift_codegen::ir::BlockArg::Value(next)],
    );

    builder.switch_to_block(found);
    let header = builder.block_params(found)[0];
    let marked = builder.ins().load(types::I8, OWNED, header, mark_offset);
    let zero = builder.ins().iconst(types::I8, 0);
    let already = builder.ins().icmp(IntCC::NotEqual, marked, zero);
    let start_scan = builder.create_block();
    builder.ins().brif(already, done, &[], start_scan, &[]);
    builder.switch_to_block(start_scan);
    let one = builder.ins().iconst(types::I8, 1);
    builder.ins().store(OWNED, one, header, mark_offset);
    let size = builder.ins().load(pointer, OWNED, header, size_offset);
    let payload = builder.ins().iadd_imm(header, payload_offset);
    let zero = builder.ins().iconst(pointer, 0);
    builder.ins().jump(
        scan,
        &[
            cranelift_codegen::ir::BlockArg::Value(payload),
            cranelift_codegen::ir::BlockArg::Value(zero),
            cranelift_codegen::ir::BlockArg::Value(size),
        ],
    );

    builder.switch_to_block(scan);
    let payload = builder.block_params(scan)[0];
    let index = builder.block_params(scan)[1];
    let size = builder.block_params(scan)[2];
    let more = builder.ins().icmp(IntCC::UnsignedLessThan, index, size);
    builder.ins().brif(more, scan_one, &[], done, &[]);

    builder.switch_to_block(scan_one);
    let address = builder.ins().iadd(payload, index);
    let child = builder.ins().load(pointer, OWNED, address, 0);
    builder.ins().call(recursive, &[child]);
    let next = builder.ins().iadd_imm(index, cell);
    builder.ins().jump(
        scan,
        &[
            cranelift_codegen::ir::BlockArg::Value(payload),
            cranelift_codegen::ir::BlockArg::Value(next),
            cranelift_codegen::ir::BlockArg::Value(size),
        ],
    );

    builder.switch_to_block(done);
    builder.ins().return_(&[]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))
}

fn define_mark_roots(
    module: &mut ObjectModule,
    pointer: Type,
    declared: FuncId,
    signature: Signature,
    roots: DataId,
    mark: FuncId,
) -> Result<(), Error> {
    let cell = i64::from(pointer.bytes());
    let size_offset = i32::try_from(cell).expect("pointer width fits in i32");

    let mut context = Context::new();
    let mut frame_context = FunctionBuilderContext::new();
    context.func.signature = signature;
    let roots = module.declare_data_in_func(roots, &mut context.func);
    let mark = module.declare_func_in_func(mark, &mut context.func);

    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame_context);
    let entry = builder.create_block();
    let frames = builder.create_block();
    let frame_slots = builder.create_block();
    let slots = builder.create_block();
    let mark_slot = builder.create_block();
    let next_frame = builder.create_block();
    let done = builder.create_block();
    builder.append_block_param(frames, pointer);
    builder.append_block_param(frame_slots, pointer);
    builder.append_block_param(slots, pointer);
    builder.append_block_param(slots, pointer);
    builder.append_block_param(slots, pointer);
    builder.append_block_param(next_frame, pointer);

    builder.switch_to_block(entry);
    let roots_address = builder.ins().global_value(pointer, roots);
    let first_frame = builder.ins().load(pointer, OWNED, roots_address, 0);
    builder.ins().jump(
        frames,
        &[cranelift_codegen::ir::BlockArg::Value(first_frame)],
    );

    builder.switch_to_block(frames);
    let frame = builder.block_params(frames)[0];
    let zero = builder.ins().iconst(pointer, 0);
    let exhausted = builder.ins().icmp(IntCC::Equal, frame, zero);
    builder.ins().brif(
        exhausted,
        done,
        &[],
        frame_slots,
        &[cranelift_codegen::ir::BlockArg::Value(frame)],
    );

    builder.switch_to_block(frame_slots);
    let frame = builder.block_params(frame_slots)[0];
    let count = builder.ins().load(pointer, OWNED, frame, size_offset);
    let zero_index = builder.ins().iconst(pointer, 0);
    builder.ins().jump(
        slots,
        &[
            cranelift_codegen::ir::BlockArg::Value(frame),
            cranelift_codegen::ir::BlockArg::Value(zero_index),
            cranelift_codegen::ir::BlockArg::Value(count),
        ],
    );

    builder.switch_to_block(slots);
    let frame = builder.block_params(slots)[0];
    let index = builder.block_params(slots)[1];
    let count = builder.block_params(slots)[2];
    let more = builder.ins().icmp(IntCC::UnsignedLessThan, index, count);
    builder.ins().brif(
        more,
        mark_slot,
        &[],
        next_frame,
        &[cranelift_codegen::ir::BlockArg::Value(frame)],
    );

    builder.switch_to_block(mark_slot);
    let offset = builder.ins().imul_imm(index, cell);
    let address = builder.ins().iadd(frame, offset);
    let candidate = builder
        .ins()
        .load(pointer, OWNED, address, size_offset * ROOT_FRAME_HEADER);
    builder.ins().call(mark, &[candidate]);
    let next = builder.ins().iadd_imm(index, 1);
    builder.ins().jump(
        slots,
        &[
            cranelift_codegen::ir::BlockArg::Value(frame),
            cranelift_codegen::ir::BlockArg::Value(next),
            cranelift_codegen::ir::BlockArg::Value(count),
        ],
    );

    builder.switch_to_block(next_frame);
    let frame = builder.block_params(next_frame)[0];
    let previous = builder.ins().load(pointer, OWNED, frame, 0);
    builder
        .ins()
        .jump(frames, &[cranelift_codegen::ir::BlockArg::Value(previous)]);

    builder.switch_to_block(done);
    builder.ins().return_(&[]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))
}

fn define_finalize(
    module: &mut ObjectModule,
    pointer: Type,
    call_conv: CallConv,
    declared: FuncId,
    signature: Signature,
    head: DataId,
    mark: FuncId,
) -> Result<(), Error> {
    let cell = i64::from(pointer.bytes());
    let cell_offset = i32::try_from(cell).expect("pointer width fits in i32");
    let mark_offset = cell_offset * 2;
    let finalized_offset = mark_offset + 1;
    let finalizer_offset = cell_offset * 3;
    let payload_offset = cell * 4;

    let mut callback = Signature::new(call_conv);
    callback.params.push(AbiParam::new(pointer));
    callback.returns.push(AbiParam::new(types::I8));

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let head = module.declare_data_in_func(head, &mut context.func);
    let mark = module.declare_func_in_func(mark, &mut context.func);
    let callback = context.func.import_signature(callback);

    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let visit = builder.create_block();
    let inspect = builder.create_block();
    let run = builder.create_block();
    let next = builder.create_block();
    let done = builder.create_block();
    builder.append_block_param(visit, pointer);
    builder.append_block_param(inspect, pointer);
    builder.append_block_param(run, pointer);
    builder.append_block_param(run, pointer);
    builder.append_block_param(next, pointer);

    builder.switch_to_block(entry);
    let head_address = builder.ins().global_value(pointer, head);
    let first = builder.ins().load(pointer, OWNED, head_address, 0);
    builder
        .ins()
        .jump(visit, &[cranelift_codegen::ir::BlockArg::Value(first)]);

    builder.switch_to_block(visit);
    let header = builder.block_params(visit)[0];
    let zero = builder.ins().iconst(pointer, 0);
    let exhausted = builder.ins().icmp(IntCC::Equal, header, zero);
    builder.ins().brif(
        exhausted,
        done,
        &[],
        inspect,
        &[cranelift_codegen::ir::BlockArg::Value(header)],
    );

    builder.switch_to_block(inspect);
    let header = builder.block_params(inspect)[0];
    let marked = builder.ins().load(types::I8, OWNED, header, mark_offset);
    let finalized = builder
        .ins()
        .load(types::I8, OWNED, header, finalized_offset);
    let function = builder.ins().load(pointer, OWNED, header, finalizer_offset);
    let zero_byte = builder.ins().iconst(types::I8, 0);
    let zero_pointer = builder.ins().iconst(pointer, 0);
    let unmarked = builder.ins().icmp(IntCC::Equal, marked, zero_byte);
    let pending = builder.ins().icmp(IntCC::Equal, finalized, zero_byte);
    let present = builder.ins().icmp(IntCC::NotEqual, function, zero_pointer);
    let eligible = builder.ins().band(unmarked, pending);
    let eligible = builder.ins().band(eligible, present);
    builder.ins().brif(
        eligible,
        run,
        &[
            cranelift_codegen::ir::BlockArg::Value(header),
            cranelift_codegen::ir::BlockArg::Value(function),
        ],
        next,
        &[cranelift_codegen::ir::BlockArg::Value(header)],
    );

    builder.switch_to_block(run);
    let header = builder.block_params(run)[0];
    let function = builder.block_params(run)[1];
    let one = builder.ins().iconst(types::I8, 1);
    builder.ins().store(OWNED, one, header, finalized_offset);
    let payload = builder.ins().iadd_imm(header, payload_offset);
    builder.ins().call(mark, &[payload]);
    builder.ins().call_indirect(callback, function, &[payload]);
    builder.ins().call(mark, &[payload]);
    builder
        .ins()
        .jump(next, &[cranelift_codegen::ir::BlockArg::Value(header)]);

    builder.switch_to_block(next);
    let header = builder.block_params(next)[0];
    let next_header = builder.ins().load(pointer, OWNED, header, 0);
    builder.ins().jump(
        visit,
        &[cranelift_codegen::ir::BlockArg::Value(next_header)],
    );

    builder.switch_to_block(done);
    builder.ins().return_(&[]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))
}

#[allow(clippy::too_many_arguments)]
fn define_collect(
    module: &mut ObjectModule,
    pointer: Type,
    declared: FuncId,
    signature: Signature,
    head: DataId,
    allocated: DataId,
    collecting: DataId,
    mark_roots: FuncId,
    finalize: FuncId,
    free: FuncId,
) -> Result<(), Error> {
    let cell = i32::try_from(pointer.bytes()).expect("pointer width fits in i32");
    let mark_offset = cell * 2;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let head = module.declare_data_in_func(head, &mut context.func);
    let allocated = module.declare_data_in_func(allocated, &mut context.func);
    let collecting = module.declare_data_in_func(collecting, &mut context.func);
    let mark_roots = module.declare_func_in_func(mark_roots, &mut context.func);
    let finalize = module.declare_func_in_func(finalize, &mut context.func);
    let free = module.declare_func_in_func(free, &mut context.func);

    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let sweep = builder.create_block();
    let inspect = builder.create_block();
    let live = builder.create_block();
    let dead = builder.create_block();
    let done = builder.create_block();
    builder.append_block_param(sweep, pointer);
    builder.append_block_param(sweep, pointer);
    builder.append_block_param(inspect, pointer);
    builder.append_block_param(inspect, pointer);

    builder.switch_to_block(entry);
    let allocated_address = builder.ins().global_value(pointer, allocated);
    let collecting_address = builder.ins().global_value(pointer, collecting);
    let zero = builder.ins().iconst(pointer, 0);
    let one = builder.ins().iconst(pointer, 1);
    builder.ins().store(OWNED, zero, allocated_address, 0);
    builder.ins().store(OWNED, one, collecting_address, 0);
    builder.ins().call(mark_roots, &[]);
    builder.ins().call(finalize, &[]);
    builder.ins().call(mark_roots, &[]);
    let head_address = builder.ins().global_value(pointer, head);
    let first = builder.ins().load(pointer, OWNED, head_address, 0);
    builder.ins().jump(
        sweep,
        &[
            cranelift_codegen::ir::BlockArg::Value(head_address),
            cranelift_codegen::ir::BlockArg::Value(first),
        ],
    );

    builder.switch_to_block(sweep);
    let link = builder.block_params(sweep)[0];
    let header = builder.block_params(sweep)[1];
    let zero = builder.ins().iconst(pointer, 0);
    let exhausted = builder.ins().icmp(IntCC::Equal, header, zero);
    builder.ins().brif(
        exhausted,
        done,
        &[],
        inspect,
        &[
            cranelift_codegen::ir::BlockArg::Value(link),
            cranelift_codegen::ir::BlockArg::Value(header),
        ],
    );

    builder.switch_to_block(inspect);
    let link = builder.block_params(inspect)[0];
    let header = builder.block_params(inspect)[1];
    let marked = builder.ins().load(types::I8, OWNED, header, mark_offset);
    let zero = builder.ins().iconst(types::I8, 0);
    let keep = builder.ins().icmp(IntCC::NotEqual, marked, zero);
    builder.ins().brif(keep, live, &[], dead, &[]);

    builder.switch_to_block(live);
    let zero = builder.ins().iconst(types::I8, 0);
    builder.ins().store(OWNED, zero, header, mark_offset);
    let next = builder.ins().load(pointer, OWNED, header, 0);
    builder.ins().jump(
        sweep,
        &[
            cranelift_codegen::ir::BlockArg::Value(header),
            cranelift_codegen::ir::BlockArg::Value(next),
        ],
    );

    builder.switch_to_block(dead);
    let next = builder.ins().load(pointer, OWNED, header, 0);
    builder.ins().store(OWNED, next, link, 0);
    builder.ins().call(free, &[header]);
    builder.ins().jump(
        sweep,
        &[
            cranelift_codegen::ir::BlockArg::Value(link),
            cranelift_codegen::ir::BlockArg::Value(next),
        ],
    );

    builder.switch_to_block(done);
    let zero = builder.ins().iconst(pointer, 0);
    builder.ins().store(OWNED, zero, collecting_address, 0);
    builder.ins().return_(&[]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))
}

#[allow(clippy::too_many_arguments)]
fn define_allocate(
    module: &mut ObjectModule,
    pointer: Type,
    declared: FuncId,
    signature: Signature,
    head: DataId,
    allocated: DataId,
    collecting: DataId,
    collect: FuncId,
    malloc: FuncId,
) -> Result<(), Error> {
    let cell = i64::from(pointer.bytes());
    let size_offset = i32::try_from(cell).expect("pointer width fits in i32");
    let mark_offset = size_offset * 2;
    let finalized_offset = mark_offset + 1;
    let finalizer_offset = size_offset * 3;
    let payload_offset = cell * 4;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let head = module.declare_data_in_func(head, &mut context.func);
    let allocated = module.declare_data_in_func(allocated, &mut context.func);
    let collecting = module.declare_data_in_func(collecting, &mut context.func);
    let collect = module.declare_func_in_func(collect, &mut context.func);
    let malloc = module.declare_func_in_func(malloc, &mut context.func);

    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let collect_now = builder.create_block();
    let allocate = builder.create_block();
    builder.append_block_params_for_function_params(entry);

    builder.switch_to_block(entry);
    let size = builder.block_params(entry)[0];
    let finalizer = builder.block_params(entry)[1];
    let allocated_address = builder.ins().global_value(pointer, allocated);
    let used = builder.ins().load(pointer, OWNED, allocated_address, 0);
    let threshold = builder.ins().iconst(pointer, COLLECT_AFTER);
    let full = builder
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, used, threshold);
    let collecting_address = builder.ins().global_value(pointer, collecting);
    let active = builder.ins().load(pointer, OWNED, collecting_address, 0);
    let zero = builder.ins().iconst(pointer, 0);
    let idle = builder.ins().icmp(IntCC::Equal, active, zero);
    let should_collect = builder.ins().band(full, idle);
    builder
        .ins()
        .brif(should_collect, collect_now, &[], allocate, &[]);

    builder.switch_to_block(collect_now);
    builder.ins().call(collect, &[]);
    builder.ins().jump(allocate, &[]);

    builder.switch_to_block(allocate);
    let total = builder.ins().iadd_imm(size, payload_offset);
    let call = builder.ins().call(malloc, &[total]);
    let header = builder.inst_results(call)[0];
    let head_address = builder.ins().global_value(pointer, head);
    let previous = builder.ins().load(pointer, OWNED, head_address, 0);
    builder.ins().store(OWNED, previous, header, 0);
    builder.ins().store(OWNED, size, header, size_offset);
    let active = builder.ins().load(pointer, OWNED, collecting_address, 0);
    let active = builder.ins().ireduce(types::I8, active);
    builder.ins().store(OWNED, active, header, mark_offset);
    let zero = builder.ins().iconst(types::I8, 0);
    builder.ins().store(OWNED, zero, header, finalized_offset);
    builder
        .ins()
        .store(OWNED, finalizer, header, finalizer_offset);
    builder.ins().store(OWNED, header, head_address, 0);

    let used = builder.ins().load(pointer, OWNED, allocated_address, 0);
    let used = builder.ins().iadd(used, total);
    builder.ins().store(OWNED, used, allocated_address, 0);
    let payload = builder.ins().iadd_imm(header, payload_offset);
    builder.ins().return_(&[payload]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))
}
