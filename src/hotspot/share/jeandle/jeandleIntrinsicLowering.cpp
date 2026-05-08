/*
 * Copyright (c) 2026, the Jeandle-JDK Authors. All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */

#include "jeandle/jeandleIntrinsicLowering.hpp"

#include "jeandle/__llvmHeadersBegin__.hpp"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InlineAsm.h"

#include "jeandle/jeandleAbstractInterpreter.hpp"
#include "jeandle/jeandleIntrinsicIRSemantics.hpp"
#include "jeandle/jeandleIntrinsicPolicy.hpp"
#include "jeandle/jeandleIntrinsicRegistry.hpp"
#include "jeandle/jeandleIntrinsicEntrypoints.hpp"
#include "jeandle/jeandleType.hpp"

#include "jeandle/__hotspotHeadersBegin__.hpp"
#include "ci/ciMethod.hpp"
#include "ci/ciSignature.hpp"
#include "jeandle/jeandle_globals.hpp"
#include "oops/arrayOop.hpp"
#include "runtime/stubRoutines.hpp"

class JeandleIntrinsicLoweringHelper : public AllStatic {
 public:
  static bool is_double_constant(llvm::Value* value, double expected,
                                 const llvm::DataLayout& data_layout) {
    llvm::Constant* constant = llvm::dyn_cast<llvm::Constant>(value);
    if (constant == nullptr) {
      if (llvm::Instruction* inst = llvm::dyn_cast<llvm::Instruction>(value)) {
        constant = llvm::ConstantFoldInstruction(inst, data_layout);
      }
    }
    if (constant == nullptr) {
      return false;
    }
    constant = llvm::ConstantFoldConstant(constant, data_layout);
    llvm::ConstantFP* fp_constant = llvm::dyn_cast<llvm::ConstantFP>(constant);
    if (fp_constant == nullptr) {
      return false;
    }
    llvm::APFloat expected_value(expected);
    return fp_constant->getValueAPF().bitwiseIsEqual(expected_value);
  }

  static void add_string_attr(llvm::CallBase& call, llvm::StringRef key, llvm::StringRef value) {
    llvm::LLVMContext& ctx = call.getContext();
    call.addAttributeAtIndex(llvm::AttributeList::FunctionIndex,
                             llvm::Attribute::get(ctx, key, value));
  }
};

void JeandleIntrinsicLowering::annotate_generated_instruction(llvm::Instruction& inst,
                                                              const JeandleIntrinsicDescriptor& desc,
                                                              const JeandleIntrinsicDecision& decision,
                                                              const JeandleIntrinsicEntrypoint* entry) const {
  JeandleIntrinsicIRSemantics::annotate_instruction(inst, desc, decision.ir_plan, entry);
}

llvm::CallInst* JeandleIntrinsicLowering::emit_runtime_call(const JeandleIntrinsicDescriptor& desc,
                                                            const JeandleIntrinsicDecision& decision,
                                                            const JeandleIntrinsicEntrypoint& entry,
                                                            llvm::ArrayRef<llvm::Value*> args) {
  llvm::SmallVector<llvm::OperandBundleDef, 1> bundles =
    JeandleIntrinsicIRSemantics::build_operand_bundles(_interp, decision.ir_plan);
  llvm::CallInst* call = _interp->create_call(entry.callee, args, entry.calling_conv, bundles);
  annotate_generated_instruction(*call, desc, decision, &entry);
  return call;
}

llvm::InvokeInst* JeandleIntrinsicLowering::emit_runtime_invoke(const JeandleIntrinsicDescriptor& desc,
                                                                const JeandleIntrinsicDecision& decision,
                                                                const JeandleIntrinsicEntrypoint& entry,
                                                                llvm::ArrayRef<llvm::Value*> args) {
  llvm::SmallVector<llvm::OperandBundleDef, 1> bundles =
    JeandleIntrinsicIRSemantics::build_operand_bundles(_interp, decision.ir_plan);
  llvm::InvokeInst* invoke = _interp->create_call_ex(entry.callee, args, entry.calling_conv, bundles);
  annotate_generated_instruction(*invoke, desc, decision, &entry);
  return invoke;
}

llvm::CallInst* JeandleIntrinsicLowering::emit_java_op_call(const JeandleIntrinsicDescriptor& desc,
                                                            const JeandleIntrinsicDecision& decision,
                                                            llvm::ArrayRef<llvm::Value*> args) {
  assert(desc.java_op_name != nullptr, "JavaOp lowering requires a JavaOp symbol");
  llvm::SmallVector<llvm::OperandBundleDef, 1> bundles =
    JeandleIntrinsicIRSemantics::build_operand_bundles(_interp, decision.ir_plan);
  llvm::CallInst* call = _interp->call_java_op(desc.java_op_name, args, bundles);
  annotate_generated_instruction(*call, desc, decision);
  JeandleIntrinsicLoweringHelper::add_string_attr(*call, "jeandle.java_op", desc.java_op_name);
  return call;
}

llvm::InvokeInst* JeandleIntrinsicLowering::emit_java_op_invoke(const JeandleIntrinsicDescriptor& desc,
                                                                const JeandleIntrinsicDecision& decision,
                                                                llvm::ArrayRef<llvm::Value*> args) {
  assert(desc.java_op_name != nullptr, "JavaOp lowering requires a JavaOp symbol");
  llvm::SmallVector<llvm::OperandBundleDef, 1> bundles =
    JeandleIntrinsicIRSemantics::build_operand_bundles(_interp, decision.ir_plan);
  llvm::InvokeInst* invoke = _interp->call_java_op_ex(desc.java_op_name, args, bundles);
  annotate_generated_instruction(*invoke, desc, decision);
  JeandleIntrinsicLoweringHelper::add_string_attr(*invoke, "jeandle.java_op", desc.java_op_name);
  return invoke;
}

bool JeandleIntrinsicLowering::lower(const JeandleIntrinsicDescriptor& desc,
                                     const JeandleIntrinsicDecision& decision,
                                     const ciMethod* target) {
  _target = target;
  // Two-level dispatch: the descriptor category selects the shared lowering
  // shape, then category-specific code switches on the precise intrinsic ID.
  switch (desc.semantics.category) {
    case JeandleIntrinsicCategory::PureMath:
      return lower_pure_math(desc, decision);
    case JeandleIntrinsicCategory::TypeCoercion:
      return lower_type_coercion(desc, decision);
    case JeandleIntrinsicCategory::LibmMath:
      if (desc.id == vmIntrinsics::_dpow) {
        return lower_pow_hybrid(desc, decision);
      }
      return lower_libm_math(desc, decision);
    case JeandleIntrinsicCategory::BarrierSemantic:
      return lower_barrier_semantic(desc, decision);
    case JeandleIntrinsicCategory::MacroSemantic:
      return lower_macro_semantic(desc, decision);
    case JeandleIntrinsicCategory::TypeSemantic:
      if (desc.id == vmIntrinsics::_getClass) {
        return lower_get_class(desc, decision);
      }
      return false;
    case JeandleIntrinsicCategory::MemorySemantic:
      if (desc.id == vmIntrinsics::_Reference_get) {
        return lower_reference_get(desc, decision);
      }
      if (desc.id == vmIntrinsics::_Reference_refersTo0 ||
          desc.id == vmIntrinsics::_PhantomReference_refersTo0) {
        return lower_reference_refers_to(desc, decision);
      }
      return false;
    case JeandleIntrinsicCategory::ArrayScan:
      return lower_count_positives(desc, decision);
    case JeandleIntrinsicCategory::AllocationSemantic:
      if (desc.id == vmIntrinsics::_newArray) {
        return lower_new_array(desc, decision);
      }
      return false;
    default:
      return false;
  }
}

bool JeandleIntrinsicLowering::lower_pure_math(const JeandleIntrinsicDescriptor& desc,
                                               const JeandleIntrinsicDecision& decision) {
  llvm::LLVMContext& ctx = *_interp->_context;
  llvm::IRBuilder<>& builder = _interp->_ir_builder;
  llvm::CallInst* call = nullptr;
  switch (desc.id) {
    case vmIntrinsics::_dabs:
      call = builder.CreateIntrinsic(JeandleType::java2llvm(T_DOUBLE, ctx), llvm::Intrinsic::fabs,
                                     {_interp->_jvm->dpop()});
      annotate_generated_instruction(*call, desc, decision);
      _interp->_jvm->dpush(call);
      return true;
    case vmIntrinsics::_fabs:
      call = builder.CreateIntrinsic(JeandleType::java2llvm(T_FLOAT, ctx), llvm::Intrinsic::fabs,
                                     {_interp->_jvm->fpop()});
      annotate_generated_instruction(*call, desc, decision);
      _interp->_jvm->fpush(call);
      return true;
    case vmIntrinsics::_iabs:
      call = builder.CreateIntrinsic(JeandleType::java2llvm(T_INT, ctx), llvm::Intrinsic::abs,
                                     {_interp->_jvm->ipop(), builder.getInt1(false)});
      annotate_generated_instruction(*call, desc, decision);
      _interp->_jvm->ipush(call);
      return true;
    case vmIntrinsics::_labs:
      call = builder.CreateIntrinsic(JeandleType::java2llvm(T_LONG, ctx), llvm::Intrinsic::abs,
                                     {_interp->_jvm->lpop(), builder.getInt1(false)});
      annotate_generated_instruction(*call, desc, decision);
      _interp->_jvm->lpush(call);
      return true;
    case vmIntrinsics::_bitCount_i:
      call = builder.CreateIntrinsic(JeandleType::java2llvm(T_INT, ctx), llvm::Intrinsic::ctpop,
                                     {_interp->_jvm->ipop()});
      annotate_generated_instruction(*call, desc, decision);
      _interp->_jvm->ipush(call);
      return true;
    case vmIntrinsics::_bitCount_l:
      call = builder.CreateIntrinsic(JeandleType::java2llvm(T_LONG, ctx), llvm::Intrinsic::ctpop,
                                     {_interp->_jvm->lpop()});
      annotate_generated_instruction(*call, desc, decision);
      // Long.bitCount(long) returns int — ctpop gives i64, trunc to i32 before pushing
      _interp->_jvm->ipush(builder.CreateTrunc(call, JeandleType::java2llvm(T_INT, ctx)));
      return true;
    case vmIntrinsics::_dsqrt:
    case vmIntrinsics::_dsqrt_strict:
      call = builder.CreateIntrinsic(JeandleType::java2llvm(T_DOUBLE, ctx), llvm::Intrinsic::sqrt,
                                     {_interp->_jvm->dpop()});
      annotate_generated_instruction(*call, desc, decision);
      _interp->_jvm->dpush(call);
      return true;
    // Rounding intrinsics: GuardedHybrid, impl_kind resolved to LLVMBuiltinCall
    // by policy after JeandleIntrinsicSupport confirmed CPU feature availability.
    case vmIntrinsics::_floor:
      call = builder.CreateIntrinsic(JeandleType::java2llvm(T_DOUBLE, ctx), llvm::Intrinsic::floor,
                                     {_interp->_jvm->dpop()});
      annotate_generated_instruction(*call, desc, decision);
      _interp->_jvm->dpush(call);
      return true;
    case vmIntrinsics::_ceil:
      call = builder.CreateIntrinsic(JeandleType::java2llvm(T_DOUBLE, ctx), llvm::Intrinsic::ceil,
                                     {_interp->_jvm->dpop()});
      annotate_generated_instruction(*call, desc, decision);
      _interp->_jvm->dpush(call);
      return true;
    case vmIntrinsics::_rint:
      call = builder.CreateIntrinsic(JeandleType::java2llvm(T_DOUBLE, ctx), llvm::Intrinsic::rint,
                                     {_interp->_jvm->dpop()});
      annotate_generated_instruction(*call, desc, decision);
      _interp->_jvm->dpush(call);
      return true;
    default:
      return false;
  }
}

bool JeandleIntrinsicLowering::lower_type_coercion(const JeandleIntrinsicDescriptor& desc,
                                                   const JeandleIntrinsicDecision& decision) {
  llvm::LLVMContext& ctx = *_interp->_context;
  llvm::IRBuilder<>& builder = _interp->_ir_builder;
  llvm::Value* cast = nullptr;
  switch (desc.id) {
    case vmIntrinsics::_floatToRawIntBits:
      cast = builder.CreateBitCast(_interp->_jvm->fpop(), builder.getInt32Ty());
      if (llvm::Instruction* inst = llvm::dyn_cast<llvm::Instruction>(cast)) {
        annotate_generated_instruction(*inst, desc, decision);
      }
      _interp->_jvm->ipush(cast);
      return true;
    case vmIntrinsics::_intBitsToFloat:
      cast = builder.CreateBitCast(_interp->_jvm->ipop(), llvm::Type::getFloatTy(ctx));
      if (llvm::Instruction* inst = llvm::dyn_cast<llvm::Instruction>(cast)) {
        annotate_generated_instruction(*inst, desc, decision);
      }
      _interp->_jvm->fpush(cast);
      return true;
    case vmIntrinsics::_doubleToRawLongBits:
      cast = builder.CreateBitCast(_interp->_jvm->dpop(), builder.getInt64Ty());
      if (llvm::Instruction* inst = llvm::dyn_cast<llvm::Instruction>(cast)) {
        annotate_generated_instruction(*inst, desc, decision);
      }
      _interp->_jvm->lpush(cast);
      return true;
    case vmIntrinsics::_longBitsToDouble:
      cast = builder.CreateBitCast(_interp->_jvm->lpop(), llvm::Type::getDoubleTy(ctx));
      if (llvm::Instruction* inst = llvm::dyn_cast<llvm::Instruction>(cast)) {
        annotate_generated_instruction(*inst, desc, decision);
      }
      _interp->_jvm->dpush(cast);
      return true;
    default:
      return false;
  }
}

bool JeandleIntrinsicLowering::lower_libm_math(const JeandleIntrinsicDescriptor& desc,
                                               const JeandleIntrinsicDecision& decision) {
  llvm::LLVMContext& ctx = *_interp->_context;
  llvm::IRBuilder<>& builder = _interp->_ir_builder;

  if (decision.impl_kind == JeandleIntrinsicImplKind::LLVMBuiltinCall) {
    llvm::Value* arg = _interp->_jvm->dpop();
    llvm::Intrinsic::ID llvm_id = llvm::Intrinsic::not_intrinsic;
    switch (desc.id) {
      case vmIntrinsics::_dsin:   llvm_id = llvm::Intrinsic::sin; break;
      case vmIntrinsics::_dcos:   llvm_id = llvm::Intrinsic::cos; break;
      case vmIntrinsics::_dtan:   llvm_id = llvm::Intrinsic::tan; break;
      case vmIntrinsics::_dlog:   llvm_id = llvm::Intrinsic::log; break;
      case vmIntrinsics::_dlog10: llvm_id = llvm::Intrinsic::log10; break;
      case vmIntrinsics::_dexp:   llvm_id = llvm::Intrinsic::exp; break;
      default: return false;
    }
    llvm::CallInst* call = builder.CreateIntrinsic(JeandleType::java2llvm(T_DOUBLE, ctx), llvm_id, {arg});
    annotate_generated_instruction(*call, desc, decision);
    _interp->_jvm->dpush(call);
    return true;
  }

  JeandleIntrinsicEntrypoint entry;
  if (!JeandleIntrinsicEntrypoints::resolve_math(desc.id, decision.impl_kind, _interp->_module, entry)) {
    return false;
  }
  llvm::Value* arg = _interp->_jvm->dpop();
  if (decision.ir_plan.needs_exception_edge) {
    _interp->_jvm->dpush(emit_runtime_invoke(desc, decision, entry, {arg}));
  } else {
    _interp->_jvm->dpush(emit_runtime_call(desc, decision, entry, {arg}));
  }
  return true;
}

bool JeandleIntrinsicLowering::lower_pow_hybrid(const JeandleIntrinsicDescriptor& desc,
                                                const JeandleIntrinsicDecision& decision) {
  llvm::IRBuilder<>& builder = _interp->_ir_builder;
  llvm::LLVMContext& ctx = *_interp->_context;

  llvm::Value* exp = _interp->_jvm->dpop();
  llvm::Value* base = _interp->_jvm->dpop();

  // Constant fast path: pow(x, 2.0) => x * x.
  // This overrides the policy decision (IRInstruction instead of LLVMBuiltinCall/HotSpotStub);
  // refine() produces accurate metadata for the emitted instruction.
  if (JeandleIntrinsicLoweringHelper::is_double_constant(exp, 2.0,
                                                         _interp->_module.getDataLayout())) {
    JeandleIntrinsicDecision refined = JeandleIntrinsicPolicy::refine(
      decision, desc, JeandleIntrinsicImplKind::IRInstruction, "pow(x,2) -> fmul");
    llvm::Value* fast = builder.CreateFMul(base, base);
    if (llvm::Instruction* inst = llvm::dyn_cast<llvm::Instruction>(fast)) {
      annotate_generated_instruction(*inst, desc, refined);
    }
    _interp->_jvm->dpush(fast);
    return true;
  }

  // Constant fast path: pow(x, 0.5) => llvm.sqrt(x) only for x > 0.0.
  if (JeandleIntrinsicLoweringHelper::is_double_constant(exp, 0.5,
                                                         _interp->_module.getDataLayout())) {
    JeandleIntrinsicDecision sqrt_decision = JeandleIntrinsicPolicy::refine(
      decision, desc, JeandleIntrinsicImplKind::LLVMBuiltinCall, "pow(x,0.5) -> llvm.sqrt");
    JeandleIntrinsicEntrypoint runtime_entry;
    if (!JeandleIntrinsicEntrypoints::resolve_math(vmIntrinsics::_dpow, decision.impl_kind,
                                                 _interp->_module, runtime_entry)) {
      return false;
    }

    llvm::Type* ret_ty = JeandleType::java2llvm(T_DOUBLE, ctx);
    llvm::Value* zero = llvm::ConstantFP::get(ret_ty, 0.0);
    llvm::BasicBlock* fast_block = llvm::BasicBlock::Create(ctx,
        "pow_0dot5_fast", _interp->_llvm_func);
    llvm::BasicBlock* slow_block = llvm::BasicBlock::Create(ctx,
        "pow_0dot5_slow", _interp->_llvm_func);
    llvm::BasicBlock* merge_block = llvm::BasicBlock::Create(ctx,
        "pow_0dot5_merge", _interp->_llvm_func);

    llvm::Value* base_gt_zero = builder.CreateFCmpOGT(base, zero, "pow.base_gt_zero");
    builder.CreateCondBr(base_gt_zero, fast_block, slow_block);

    builder.SetInsertPoint(fast_block);
    llvm::CallInst* fast = builder.CreateIntrinsic(ret_ty, llvm::Intrinsic::sqrt, {base});
    annotate_generated_instruction(*fast, desc, sqrt_decision);
    builder.CreateBr(merge_block);

    builder.SetInsertPoint(slow_block);
    JeandleIntrinsicDecision runtime_decision = JeandleIntrinsicPolicy::refine(
        decision, desc, JeandleIntrinsicImplKind::HotSpotStub, "pow(x,0.5) slow -> runtime");
    llvm::Value* slow = emit_runtime_call(desc, runtime_decision, runtime_entry, {base, exp});
    builder.CreateBr(merge_block);

    builder.SetInsertPoint(merge_block);
    _interp->_block->set_tail_llvm_block(merge_block);
    llvm::PHINode* result = builder.CreatePHI(ret_ty, 2, "pow_0dot5.result");
    result->addIncoming(fast, fast_block);
    result->addIncoming(slow, slow_block);
    _interp->_jvm->dpush(result);
    return true;
  }

  // General path: use the impl_kind that policy already resolved.
  // For LLVMBuiltinCall policy chose llvm.pow; for HotSpotStub/SharedRuntime delegate to runtime.
  if (decision.impl_kind == JeandleIntrinsicImplKind::LLVMBuiltinCall) {
    llvm::Function* pow_fn =
      llvm::Intrinsic::getOrInsertDeclaration(&_interp->_module, llvm::Intrinsic::pow,
                                              {JeandleType::java2llvm(T_DOUBLE, ctx)});
    llvm::CallInst* call = builder.CreateCall(pow_fn, {base, exp});
    annotate_generated_instruction(*call, desc, decision);
    _interp->_jvm->dpush(call);
    return true;
  }

  JeandleIntrinsicEntrypoint entry;
  if (!JeandleIntrinsicEntrypoints::resolve_math(vmIntrinsics::_dpow, decision.impl_kind, _interp->_module, entry)) {
    return false;
  }
  if (decision.ir_plan.needs_exception_edge) {
    _interp->_jvm->dpush(emit_runtime_invoke(desc, decision, entry, {base, exp}));
  } else {
    _interp->_jvm->dpush(emit_runtime_call(desc, decision, entry, {base, exp}));
  }
  return true;
}

bool JeandleIntrinsicLowering::lower_get_class(const JeandleIntrinsicDescriptor& desc,
                                               const JeandleIntrinsicDecision& decision) {
  llvm::Value* obj = _interp->_jvm->apop();
  llvm::CallBase* result = nullptr;
  if (decision.ir_plan.needs_exception_edge) {
    result = emit_java_op_invoke(desc, decision, {obj});
  } else {
    result = emit_java_op_call(desc, decision, {obj});
  }
  _interp->_jvm->apush(result);
  return true;
}

bool JeandleIntrinsicLowering::lower_reference_get(const JeandleIntrinsicDescriptor& desc,
                                                   const JeandleIntrinsicDecision& decision) {
  llvm::Value* reference = _interp->_jvm->apop();
  llvm::CallBase* result = nullptr;
  if (decision.ir_plan.needs_exception_edge) {
    result = emit_java_op_invoke(desc, decision, {reference});
  } else {
    result = emit_java_op_call(desc, decision, {reference});
  }
  _interp->_jvm->apush(result);
  return true;
}

bool JeandleIntrinsicLowering::lower_barrier_semantic(const JeandleIntrinsicDescriptor& desc,
                                                      const JeandleIntrinsicDecision& decision) {
  llvm::IRBuilder<>& builder = _interp->_ir_builder;
  llvm::AtomicOrdering ordering;
  switch (desc.id) {
    case vmIntrinsics::_loadFence:  ordering = llvm::AtomicOrdering::Acquire;                break;
    case vmIntrinsics::_storeFence: ordering = llvm::AtomicOrdering::Release;                break;
    case vmIntrinsics::_fullFence:  ordering = llvm::AtomicOrdering::SequentiallyConsistent; break;
    default: return false;
  }
  _interp->_jvm->apop(); // Unsafe receiver (invokevirtual, no other args)
  llvm::FenceInst* fence = builder.CreateFence(ordering);
  annotate_generated_instruction(*fence, desc, decision);
  return true;
}

bool JeandleIntrinsicLowering::lower_macro_semantic(const JeandleIntrinsicDescriptor& desc,
                                                    const JeandleIntrinsicDecision& decision) {
  switch (desc.id) {
    case vmIntrinsics::_onSpinWait:
      return lower_spin_wait_hint(desc, decision);
    case vmIntrinsics::_Preconditions_checkIndex:
    case vmIntrinsics::_Preconditions_checkLongIndex:
      return lower_preconditions_check_index(desc, decision);
    case vmIntrinsics::_blackhole:
      return lower_blackhole(desc, decision);
    default:
      return false;
  }
}

// Preconditions.checkIndex(int|long index, int|long length, BiFunction exceptionFactory)
//   -> int|long
//
// The condition to guard is: index < 0 || index >= length
//
// Naive single unsigned compare (uint)index >= (uint)length only works when
// length >= 0.  When length < 0 the unsigned value is huge so any non-negative
// index passes the check — wrong.
//
// Correct guard: length < 0 || (uint)index >= (uint)length
//   • length < 0 fires unconditionally when the caller passes a negative bound.
//   • (uint)index >= (uint)length, given length >= 0, covers index < 0 (negative
//     index becomes a large unsigned value) and index >= length.
//
// This aligns with C2: C2 uses the unsigned shortcut only after range analysis
// has proved length >= 0; without that proof it guards length explicitly.
// C1 uses two separate signed comparisons — semantically equivalent.
//
// On the pass path we emit two llvm.assume calls to tell the optimiser that the
// return value (index) satisfies  0 <= index < length.  This allows LLVM to fold
// downstream array bounds checks that use the same index.
bool JeandleIntrinsicLowering::lower_preconditions_check_index(
    const JeandleIntrinsicDescriptor& desc,
    const JeandleIntrinsicDecision& decision) {
  llvm::IRBuilder<>& builder = _interp->_ir_builder;
  llvm::LLVMContext& ctx = *_interp->_context;
  int cur_bci = _interp->_bytecodes.cur_bci();
  bool is_long = desc.id == vmIntrinsics::_Preconditions_checkLongIndex;

  // Stack (top-of-stack first): exceptionFactory (aref), length (int|long),
  // index (int|long).
  // Use logical-value peeks so the stack remains intact when uncommon_trap
  // captures the deopt bundle via create_current_deopt_bundle() ->
  // _jvm->deopt_args(). This is required for the long variant because Jeandle's
  // operand stack models long values with an extra null high-slot placeholder.
  // The actual pops are deferred to the pass path below, matching the pattern
  // used by do_array_load / do_array_store / instanceof.
  llvm::Value* exception_factory = _interp->_jvm->peek_value(0).value(); // BiFunction — not used in fast path
  llvm::Value* length            = _interp->_jvm->peek_value(1).value();
  llvm::Value* index             = _interp->_jvm->peek_value(2).value();
  (void)exception_factory;

  llvm::Type* integer_ty = is_long ? llvm::Type::getInt64Ty(ctx)
                                   : llvm::Type::getInt32Ty(ctx);
  llvm::Value* zero = llvm::ConstantInt::get(integer_ty, 0);

  // Create the guard blocks.
  //
  // Two-level check to distinguish precondition failure (length < 0) from
  // true range failure (index out of bounds), mirroring C2's distinction
  // between Reason_intrinsic and Reason_range_check.
  //
  // Control flow:
  //   entry ─(len<0)──► fail_pre  [Reason_intrinsic]
  //         ─(len≥0)──► mid
  //                       ─(idx oob)──► fail_range  [Reason_range_check]
  //                       ─(in range)──► pass
  llvm::BasicBlock* pass = llvm::BasicBlock::Create(ctx,
      "bci_" + std::to_string(cur_bci) + "_checkIndex_pass", _interp->_llvm_func);
  llvm::BasicBlock* mid  = llvm::BasicBlock::Create(ctx,
      "bci_" + std::to_string(cur_bci) + "_checkIndex_mid", _interp->_llvm_func);
  llvm::BasicBlock* fail_pre = llvm::BasicBlock::Create(ctx,
      "bci_" + std::to_string(cur_bci) + "_checkIndex_fail_pre", _interp->_llvm_func);
  llvm::BasicBlock* fail_range = llvm::BasicBlock::Create(ctx,
      "bci_" + std::to_string(cur_bci) + "_checkIndex_fail_range", _interp->_llvm_func);

  // First guard: length < 0 → precondition failure.
  llvm::Value* len_neg = builder.CreateICmp(llvm::CmpInst::ICMP_SLT, length, zero,
                                            "checkIndex.len_neg");
  llvm::BranchInst* br_len = builder.CreateCondBr(len_neg, fail_pre, mid);
  annotate_generated_instruction(*br_len, desc, decision);

  // mid: length >= 0 is guaranteed here; unsigned compare covers index < 0 and index >= length.
  builder.SetInsertPoint(mid);
  llvm::Value* idx_oob = builder.CreateICmp(llvm::CmpInst::ICMP_UGE, index, length,
                                            "checkIndex.idx_oob");
  llvm::BranchInst* br_idx = builder.CreateCondBr(idx_oob, fail_range, pass);
  annotate_generated_instruction(*br_idx, desc, decision);

  // fail_pre: intrinsic precondition failed (length < 0).
  // Mirrors C2's Reason_intrinsic path; too_many_traps of this reason triggers
  // NormalInvoke fallback in decide() above.
  _interp->uncommon_trap(Deoptimization::Reason_intrinsic,
                         Deoptimization::Action_maybe_recompile, fail_pre);

  // fail_range: true range check failure (index out of bounds).
  _interp->uncommon_trap(Deoptimization::Reason_range_check,
                         Deoptimization::Action_maybe_recompile, fail_range);

  // Pass path: guards passed — consume the three invokevirtual arguments, then
  // push the validated index as the intrinsic's return value.
  builder.SetInsertPoint(pass);
  _interp->_block->set_tail_llvm_block(pass);
  _interp->_jvm->apop(); // exception_factory
  if (is_long) {
    _interp->_jvm->lpop(); // length
    _interp->_jvm->lpop(); // index (value already captured via raw_peek above)
  } else {
    _interp->_jvm->ipop(); // length
    _interp->_jvm->ipop(); // index (value already captured via raw_peek above)
  }

  // Express  length >= 0, 0 <= index < length  as llvm.assume facts.
  // These serve as supplementary hints for SCEV, LVI, and CVP:
  //   - assume(length >= 0): supplements the control-flow fact established in
  //     mid block; helps SCEV and LVI when length is used downstream.
  //   - assume(index >= 0) + assume(index < length): let CVP eliminate a
  //     boundary_check whose arr_len is GVN-proved equal to length.
  //
  // TODO: llvm.assume has fragile propagation semantics — these
  // facts are block-local annotations that do not flow through def-use chains
  // across calls or PHI merges.  A more robust future approach is to introduce
  // a @llvm.jeandle.checked_index refined-value intrinsic (analogous to C2's
  // ConstraintCastNode) that carries the range fact in the def-use chain itself,
  // consumed by a dedicated Jeandle BCE pass.  Until then, the assumes below
  // serve as the primary range-fact delivery mechanism.
  llvm::Value* len_nonneg = builder.CreateICmp(llvm::CmpInst::ICMP_SGE, length, zero,
                                               "checkIndex.len_nonneg");
  llvm::Value* non_neg    = builder.CreateICmp(llvm::CmpInst::ICMP_SGE, index, zero,
                                               "checkIndex.nonneg");
  llvm::Value* below_len  = builder.CreateICmp(llvm::CmpInst::ICMP_SLT, index, length,
                                               "checkIndex.below_len");
  builder.CreateIntrinsic(llvm::Intrinsic::assume, llvm::ArrayRef<llvm::Type*>{}, {len_nonneg});
  builder.CreateIntrinsic(llvm::Intrinsic::assume, llvm::ArrayRef<llvm::Type*>{}, {non_neg});
  builder.CreateIntrinsic(llvm::Intrinsic::assume, llvm::ArrayRef<llvm::Type*>{}, {below_len});

  if (is_long) {
    _interp->_jvm->lpush(index);
  } else {
    _interp->_jvm->ipush(index);
  }
  return true;
}

bool JeandleIntrinsicLowering::lower_reference_refers_to(const JeandleIntrinsicDescriptor& desc,
                                                          const JeandleIntrinsicDecision& decision) {
  // Stack order: ..., reference (this), obj — pop in reverse
  llvm::Value* obj = _interp->_jvm->apop();
  llvm::Value* reference = _interp->_jvm->apop();
  llvm::CallBase* result = nullptr;
  if (decision.ir_plan.needs_exception_edge) {
    result = emit_java_op_invoke(desc, decision, {reference, obj});
  } else {
    result = emit_java_op_call(desc, decision, {reference, obj});
  }
  // JavaOp returns i32 (JVM boolean convention); push as int
  _interp->_jvm->ipush(result);
  return true;
}

// StringCoding.countPositives(byte[] ba, int off, int len) → int
//
// Computes ba_start = &ba[off] and delegates to count_positives_impl(ba_start, len)
// via a RuntimeLeafCall (gc-leaf, no safepoint, no exception).
//
// Stack order (top-of-stack first): len (int), off (int), ba (aref).
// No receiver — static method.
//
// Guards (deopt → interpreter re-executes the call):
//   ba != null  |  off >= 0  |  len >= 0  |  off + len <= ba.length
bool JeandleIntrinsicLowering::lower_count_positives(
    const JeandleIntrinsicDescriptor& desc,
    const JeandleIntrinsicDecision& decision) {
  llvm::IRBuilder<>& builder = _interp->_ir_builder;
  llvm::LLVMContext& ctx = *_interp->_context;

  // Peek without popping so the jvm stack is intact when string_range_check
  // emits uncommon_trap calls (each trap captures the deopt bundle from the
  // current stack state, which must still hold all three arguments).
  llvm::Value* len = _interp->_jvm->raw_peek(0).value(); // top of stack
  llvm::Value* off = _interp->_jvm->raw_peek(1).value();
  llvm::Value* ba  = _interp->_jvm->raw_peek(2).value();

  // Emit guards: null-check ba, off >= 0, len >= 0, off + len <= ba.length.
  // Any failing guard deopt-traps and the interpreter retries the invokestatic.
  _interp->string_range_check(ba, off, len);

  // All guards passed — consume the three invokestatic arguments.
  _interp->_jvm->ipop(); // len
  _interp->_jvm->ipop(); // off
  _interp->_jvm->apop(); // ba

  // Compute ba_start = ba + array_base_offset_in_bytes(T_BYTE) + off.
  // array_base_offset is the size of the array object header; adding it gives
  // a pointer to ba[0].  Adding off then yields ba[off].
  llvm::Value* base_off   = builder.getInt32(arrayOopDesc::base_offset_in_bytes(T_BYTE));
  llvm::Value* array_base = builder.CreateInBoundsPtrAdd(ba, base_off, "ba_base");
  llvm::Value* ba_start   = builder.CreateInBoundsGEP(
      llvm::Type::getInt8Ty(ctx), array_base, off, "ba_start");

  JeandleIntrinsicEntrypoint entry;
  if (!JeandleIntrinsicEntrypoints::resolve_count_positives(_interp->_module, entry)) {
    return false;
  }
  llvm::CallInst* result = emit_runtime_call(desc, decision, entry, {ba_start, len});
  _interp->_jvm->ipush(result);
  return true;
}

// _blackhole: consume all arguments via volatile inline asm to prevent DCE.
// Each argument is passed through "r,~{memory}" volatile asm so LLVM cannot
// eliminate the computation that produced it.  Float/double are bitcast to
// integer types first because "r" is an integer register constraint.
// The receiver (if any) is consumed last after all typed parameters.
bool JeandleIntrinsicLowering::lower_blackhole(const JeandleIntrinsicDescriptor& desc,
                                               const JeandleIntrinsicDecision& decision) {
  llvm::IRBuilder<>& builder = _interp->_ir_builder;
  llvm::LLVMContext& ctx = *_interp->_context;

  ciSignature* sig = _target->signature();

  // Pop parameters in reverse order (last param = top of stack).
  for (int i = sig->count() - 1; i >= 0; i--) {
    BasicType bt = sig->type_at(i)->basic_type();
    llvm::Value* val;
    switch (bt) {
      case T_INT: case T_BOOLEAN: case T_BYTE: case T_CHAR: case T_SHORT:
        val = _interp->_jvm->ipop();
        break;
      case T_LONG:
        val = _interp->_jvm->lpop();
        break;
      case T_FLOAT:
        val = builder.CreateBitCast(_interp->_jvm->fpop(), builder.getInt32Ty());
        break;
      case T_DOUBLE:
        val = builder.CreateBitCast(_interp->_jvm->dpop(), builder.getInt64Ty());
        break;
      case T_OBJECT: case T_ARRAY:
        val = _interp->_jvm->apop();
        break;
      default:
        return false;
    }
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(ctx), {val->getType()}, false);
    // No ~{memory} clobber: blackhole must keep SSA values live (prevent DCE)
    // but must not act as a memory barrier. C2 models this as a control-only
    // use with no memory effects; omitting ~{memory} preserves that contract
    // so LLVM can still move loads/stores freely across the blackhole call.
    auto* ia = llvm::InlineAsm::get(fn_ty, "", "r",
                                    /*hasSideEffects=*/true);
    llvm::CallInst* call = builder.CreateCall(ia, {val});
    annotate_generated_instruction(*call, desc, decision);
  }

  // Consume the receiver for non-static blackhole calls.
  if (!_target->is_static()) {
    _interp->_jvm->apop();
  }

  // void return: nothing to push on the JVM operand stack
  return true;
}

// Array.newInstance(Class<?> componentType, int length) → Object
//
// Stack (top-of-stack first): length (int), componentType (oop).
// Static method — no receiver.
//
// Delegates to jeandle.new_array(mirror, length) JavaOp which:
//   1. Loads the cached array klass from the mirror with acquire ordering.
//   2. Fast path (klass non-null): calls new_array_callee(klass, length, thread).
//   3. Slow path (klass null):     calls new_array_from_mirror_callee(mirror, length, thread)
//      which invokes Reflection::reflect_new_array — handles klass resolution, primitive
//      types, dimension limits, NegativeArraySizeException, NullPointerException.
//
// uses emit_java_op_invoke when needs_exception_edge is set (exceptions may propagate).
bool JeandleIntrinsicLowering::lower_new_array(const JeandleIntrinsicDescriptor& desc,
                                               const JeandleIntrinsicDecision& decision) {
  llvm::Value* length = _interp->_jvm->ipop();
  llvm::Value* mirror = _interp->_jvm->apop();

  llvm::CallBase* result;
  if (decision.ir_plan.needs_exception_edge) {
    result = emit_java_op_invoke(desc, decision, {mirror, length});
  } else {
    result = emit_java_op_call(desc, decision, {mirror, length});
  }
  _interp->_jvm->apush(result);
  return true;
}
