//! A map's table (LR13.2): open addressing over buckets of
//! [`layout::BUCKET_BYTES`], probing one bucket at a time, never more than
//! three quarters full so a probe always ends.
//!
//! Keys are words. `text` says whether two are the same when their text is
//! rather than when the words are.

use cranelift_codegen::Context;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    AbiParam, BlockArg, InstBuilder, MemFlags, Signature, Type, Value, types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::ObjectModule;

use crate::Error;
use crate::layout;

const OWNED: MemFlags = MemFlags::trusted();

pub(crate) struct Table {
    /// `(map, key, hash, text) -> bucket`, or null.
    pub find: FuncId,
    /// `(map, key, hash, text) -> bucket`, claimed where the map had none.
    /// It may allocate, so the map has to be reachable from a root.
    pub insert: FuncId,
}

pub(crate) fn emit(
    module: &mut ObjectModule,
    pointer: Type,
    call_conv: CallConv,
    allocate: FuncId,
    text_equal: FuncId,
) -> Result<Table, Error> {
    let find = define_find(module, pointer, call_conv, text_equal)?;
    let place = define_place(module, pointer, call_conv)?;
    let insert = define_insert(module, pointer, call_conv, allocate, find, place)?;
    Ok(Table { find, insert })
}

fn signature(pointer: Type, call_conv: CallConv) -> Signature {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(types::I8));
    signature.returns.push(AbiParam::new(pointer));
    signature
}

fn bucket_at(builder: &mut FunctionBuilder<'_>, buckets: Value, index: Value) -> Value {
    let offset = builder.ins().imul_imm(index, layout::BUCKET_BYTES);
    builder.ins().iadd(buckets, offset)
}

fn define_find(
    module: &mut ObjectModule,
    pointer: Type,
    call_conv: CallConv,
    text_equal: FuncId,
) -> Result<FuncId, Error> {
    let signature = signature(pointer, call_conv);
    let declared = module
        .declare_function("luar_map_find", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let text_equal = module.declare_func_in_func(text_equal, &mut context.func);
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let probe = builder.create_block();
    let check_hash = builder.create_block();
    let check_key = builder.create_block();
    let compare_text = builder.create_block();
    let compare_word = builder.create_block();
    let decide = builder.create_block();
    let next = builder.create_block();
    let hit = builder.create_block();
    let miss = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(probe, pointer);
    builder.append_block_param(check_hash, pointer);
    builder.append_block_param(check_key, pointer);
    builder.append_block_param(compare_text, pointer);
    builder.append_block_param(compare_word, pointer);
    builder.append_block_param(decide, pointer);
    builder.append_block_param(decide, types::I8);
    builder.append_block_param(next, pointer);
    builder.append_block_param(hit, pointer);

    builder.switch_to_block(entry);
    let map = builder.block_params(entry)[0];
    let key = builder.block_params(entry)[1];
    let hash = builder.block_params(entry)[2];
    let text = builder.block_params(entry)[3];
    let capacity = builder.ins().load(pointer, OWNED, map, layout::CAPACITY);
    let buckets = builder.ins().load(pointer, OWNED, map, layout::BUFFER);
    let mask = builder.ins().iadd_imm(capacity, -1);
    let first = builder.ins().band(hash, mask);
    let empty = builder.ins().icmp_imm(IntCC::Equal, capacity, 0);
    builder
        .ins()
        .brif(empty, miss, &[], probe, &[BlockArg::Value(first)]);

    builder.switch_to_block(probe);
    let index = builder.block_params(probe)[0];
    let bucket = bucket_at(&mut builder, buckets, index);
    let occupied = builder
        .ins()
        .load(pointer, OWNED, bucket, layout::BUCKET_OCCUPIED);
    let vacant = builder.ins().icmp_imm(IntCC::Equal, occupied, 0);
    builder
        .ins()
        .brif(vacant, miss, &[], check_hash, &[BlockArg::Value(index)]);

    builder.switch_to_block(check_hash);
    let index = builder.block_params(check_hash)[0];
    let bucket = bucket_at(&mut builder, buckets, index);
    let stored_hash = builder
        .ins()
        .load(pointer, OWNED, bucket, layout::BUCKET_HASH);
    let same_hash = builder.ins().icmp(IntCC::Equal, stored_hash, hash);
    builder.ins().brif(
        same_hash,
        check_key,
        &[BlockArg::Value(index)],
        next,
        &[BlockArg::Value(index)],
    );

    builder.switch_to_block(check_key);
    let index = builder.block_params(check_key)[0];
    let is_text = builder.ins().icmp_imm(IntCC::NotEqual, text, 0);
    builder.ins().brif(
        is_text,
        compare_text,
        &[BlockArg::Value(index)],
        compare_word,
        &[BlockArg::Value(index)],
    );

    builder.switch_to_block(compare_text);
    let index = builder.block_params(compare_text)[0];
    let bucket = bucket_at(&mut builder, buckets, index);
    let stored_key = builder
        .ins()
        .load(pointer, OWNED, bucket, layout::BUCKET_KEY);
    let call = builder.ins().call(text_equal, &[stored_key, key]);
    let same = builder.inst_results(call)[0];
    builder
        .ins()
        .jump(decide, &[BlockArg::Value(index), BlockArg::Value(same)]);

    builder.switch_to_block(compare_word);
    let index = builder.block_params(compare_word)[0];
    let bucket = bucket_at(&mut builder, buckets, index);
    let stored_key = builder
        .ins()
        .load(pointer, OWNED, bucket, layout::BUCKET_KEY);
    let same = builder.ins().icmp(IntCC::Equal, stored_key, key);
    builder
        .ins()
        .jump(decide, &[BlockArg::Value(index), BlockArg::Value(same)]);

    builder.switch_to_block(decide);
    let index = builder.block_params(decide)[0];
    let same = builder.block_params(decide)[1];
    builder.ins().brif(
        same,
        hit,
        &[BlockArg::Value(index)],
        next,
        &[BlockArg::Value(index)],
    );

    builder.switch_to_block(next);
    let index = builder.block_params(next)[0];
    let following = builder.ins().iadd_imm(index, 1);
    let following = builder.ins().band(following, mask);
    builder.ins().jump(probe, &[BlockArg::Value(following)]);

    builder.switch_to_block(hit);
    let index = builder.block_params(hit)[0];
    let bucket = bucket_at(&mut builder, buckets, index);
    builder.ins().return_(&[bucket]);

    builder.switch_to_block(miss);
    let null = builder.ins().iconst(pointer, 0);
    builder.ins().return_(&[null]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

/// `(buckets, capacity, key, hash) -> bucket`: claims the first vacant bucket
/// on the probe path of a key the table does not hold.
fn define_place(
    module: &mut ObjectModule,
    pointer: Type,
    call_conv: CallConv,
) -> Result<FuncId, Error> {
    let mut signature = Signature::new(call_conv);
    for _ in 0..4 {
        signature.params.push(AbiParam::new(pointer));
    }
    signature.returns.push(AbiParam::new(pointer));
    let declared = module
        .declare_function("luar_map_place", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let probe = builder.create_block();
    let next = builder.create_block();
    let claim = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(probe, pointer);
    builder.append_block_param(next, pointer);
    builder.append_block_param(claim, pointer);

    builder.switch_to_block(entry);
    let buckets = builder.block_params(entry)[0];
    let capacity = builder.block_params(entry)[1];
    let key = builder.block_params(entry)[2];
    let hash = builder.block_params(entry)[3];
    let mask = builder.ins().iadd_imm(capacity, -1);
    let first = builder.ins().band(hash, mask);
    builder.ins().jump(probe, &[BlockArg::Value(first)]);

    builder.switch_to_block(probe);
    let index = builder.block_params(probe)[0];
    let bucket = bucket_at(&mut builder, buckets, index);
    let occupied = builder
        .ins()
        .load(pointer, OWNED, bucket, layout::BUCKET_OCCUPIED);
    let vacant = builder.ins().icmp_imm(IntCC::Equal, occupied, 0);
    builder.ins().brif(
        vacant,
        claim,
        &[BlockArg::Value(index)],
        next,
        &[BlockArg::Value(index)],
    );

    builder.switch_to_block(next);
    let index = builder.block_params(next)[0];
    let following = builder.ins().iadd_imm(index, 1);
    let following = builder.ins().band(following, mask);
    builder.ins().jump(probe, &[BlockArg::Value(following)]);

    builder.switch_to_block(claim);
    let index = builder.block_params(claim)[0];
    let bucket = bucket_at(&mut builder, buckets, index);
    let one = builder.ins().iconst(pointer, 1);
    builder
        .ins()
        .store(OWNED, one, bucket, layout::BUCKET_OCCUPIED);
    builder.ins().store(OWNED, key, bucket, layout::BUCKET_KEY);
    builder
        .ins()
        .store(OWNED, hash, bucket, layout::BUCKET_HASH);
    builder.ins().return_(&[bucket]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}

/// A map that would pass three quarters full doubles its table first.
fn define_insert(
    module: &mut ObjectModule,
    pointer: Type,
    call_conv: CallConv,
    allocate: FuncId,
    find: FuncId,
    place: FuncId,
) -> Result<FuncId, Error> {
    let signature = signature(pointer, call_conv);
    let declared = module
        .declare_function("luar_map_insert", Linkage::Local, &signature)
        .map_err(|error| Error::Cranelift(error.to_string()))?;

    let mut context = Context::new();
    let mut frame = FunctionBuilderContext::new();
    context.func.signature = signature;
    let allocate = module.declare_func_in_func(allocate, &mut context.func);
    let find = module.declare_func_in_func(find, &mut context.func);
    let place = module.declare_func_in_func(place, &mut context.func);
    let mut builder = FunctionBuilder::new(&mut context.func, &mut frame);
    let entry = builder.create_block();
    let check = builder.create_block();
    let grow = builder.create_block();
    let clear = builder.create_block();
    let clear_one = builder.create_block();
    let rehash = builder.create_block();
    let rehash_one = builder.create_block();
    let carry = builder.create_block();
    let swap = builder.create_block();
    let claim = builder.create_block();
    let done = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.append_block_param(clear, pointer);
    builder.append_block_param(clear_one, pointer);
    builder.append_block_param(rehash, pointer);
    builder.append_block_param(rehash_one, pointer);
    builder.append_block_param(carry, pointer);
    builder.append_block_param(done, pointer);

    builder.switch_to_block(entry);
    let map = builder.block_params(entry)[0];
    let key = builder.block_params(entry)[1];
    let hash = builder.block_params(entry)[2];
    let text = builder.block_params(entry)[3];
    let call = builder.ins().call(find, &[map, key, hash, text]);
    let found = builder.inst_results(call)[0];
    let present = builder.ins().icmp_imm(IntCC::NotEqual, found, 0);
    builder
        .ins()
        .brif(present, done, &[BlockArg::Value(found)], check, &[]);

    builder.switch_to_block(check);
    let count = builder.ins().load(pointer, OWNED, map, layout::LENGTH);
    let capacity = builder.ins().load(pointer, OWNED, map, layout::CAPACITY);
    let old_buckets = builder.ins().load(pointer, OWNED, map, layout::BUFFER);
    let after = builder.ins().iadd_imm(count, 1);
    let needed = builder.ins().imul_imm(after, 4);
    let room = builder.ins().imul_imm(capacity, 3);
    let full = builder.ins().icmp(IntCC::UnsignedGreaterThan, needed, room);
    builder.ins().brif(full, grow, &[], claim, &[]);

    builder.switch_to_block(grow);
    let doubled = builder.ins().imul_imm(capacity, 2);
    let least = builder.ins().iconst(pointer, 4);
    let small = builder.ins().icmp(IntCC::UnsignedLessThan, doubled, least);
    let grown = builder.ins().select(small, least, doubled);
    let bytes = builder.ins().imul_imm(grown, layout::BUCKET_BYTES);
    let no_finalizer = builder.ins().iconst(pointer, 0);
    let call = builder.ins().call(allocate, &[bytes, no_finalizer]);
    let fresh = builder.inst_results(call)[0];
    let zero = builder.ins().iconst(pointer, 0);
    builder.ins().jump(clear, &[BlockArg::Value(zero)]);

    builder.switch_to_block(clear);
    let index = builder.block_params(clear)[0];
    let more = builder.ins().icmp(IntCC::UnsignedLessThan, index, grown);
    let zero = builder.ins().iconst(pointer, 0);
    builder.ins().brif(
        more,
        clear_one,
        &[BlockArg::Value(index)],
        rehash,
        &[BlockArg::Value(zero)],
    );

    builder.switch_to_block(clear_one);
    let index = builder.block_params(clear_one)[0];
    let bucket = bucket_at(&mut builder, fresh, index);
    let zero = builder.ins().iconst(pointer, 0);
    builder
        .ins()
        .store(OWNED, zero, bucket, layout::BUCKET_OCCUPIED);
    let following = builder.ins().iadd_imm(index, 1);
    builder.ins().jump(clear, &[BlockArg::Value(following)]);

    builder.switch_to_block(rehash);
    let index = builder.block_params(rehash)[0];
    let more = builder.ins().icmp(IntCC::UnsignedLessThan, index, capacity);
    builder
        .ins()
        .brif(more, rehash_one, &[BlockArg::Value(index)], swap, &[]);

    builder.switch_to_block(rehash_one);
    let index = builder.block_params(rehash_one)[0];
    let old = bucket_at(&mut builder, old_buckets, index);
    let occupied = builder
        .ins()
        .load(pointer, OWNED, old, layout::BUCKET_OCCUPIED);
    let held = builder.ins().icmp_imm(IntCC::NotEqual, occupied, 0);
    let following = builder.ins().iadd_imm(index, 1);
    builder.ins().brif(
        held,
        carry,
        &[BlockArg::Value(index)],
        rehash,
        &[BlockArg::Value(following)],
    );

    builder.switch_to_block(carry);
    let index = builder.block_params(carry)[0];
    let old = bucket_at(&mut builder, old_buckets, index);
    let old_key = builder.ins().load(pointer, OWNED, old, layout::BUCKET_KEY);
    let old_hash = builder.ins().load(pointer, OWNED, old, layout::BUCKET_HASH);
    let old_value = builder
        .ins()
        .load(pointer, OWNED, old, layout::BUCKET_VALUE);
    let call = builder
        .ins()
        .call(place, &[fresh, grown, old_key, old_hash]);
    let moved = builder.inst_results(call)[0];
    builder
        .ins()
        .store(OWNED, old_value, moved, layout::BUCKET_VALUE);
    let following = builder.ins().iadd_imm(index, 1);
    builder.ins().jump(rehash, &[BlockArg::Value(following)]);

    builder.switch_to_block(swap);
    builder.ins().store(OWNED, fresh, map, layout::BUFFER);
    builder.ins().store(OWNED, grown, map, layout::CAPACITY);
    builder.ins().jump(claim, &[]);

    builder.switch_to_block(claim);
    let buckets = builder.ins().load(pointer, OWNED, map, layout::BUFFER);
    let capacity = builder.ins().load(pointer, OWNED, map, layout::CAPACITY);
    let call = builder.ins().call(place, &[buckets, capacity, key, hash]);
    let bucket = builder.inst_results(call)[0];
    let count = builder.ins().load(pointer, OWNED, map, layout::LENGTH);
    let count = builder.ins().iadd_imm(count, 1);
    builder.ins().store(OWNED, count, map, layout::LENGTH);
    builder.ins().jump(done, &[BlockArg::Value(bucket)]);

    builder.switch_to_block(done);
    let bucket = builder.block_params(done)[0];
    builder.ins().return_(&[bucket]);
    builder.seal_all_blocks();
    builder.finalize();
    module
        .define_function(declared, &mut context)
        .map_err(|error| Error::Cranelift(error.to_string()))?;
    Ok(declared)
}
