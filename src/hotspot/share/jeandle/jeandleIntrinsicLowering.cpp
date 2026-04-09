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
#include "llvm/IR/Constants.h"

#include "jeandle/jeandleAbstractInterpreter.hpp"
#include "jeandle/jeandleIntrinsicIRSemantics.hpp"
#include "jeandle/jeandleIntrinsicPolicy.hpp"
#include "jeandle/jeandleIntrinsicRegistry.hpp"
#include "jeandle/jeandleRuntimeEntrypoints.hpp"
#include "jeandle/jeandleType.hpp"

#include "jeandle/__hotspotHeadersBegin__.hpp"
#include "ci/ciMethod.hpp"
#include "jeandle/jeandle_globals.hpp"
#include "runtime/stubRoutines.hpp"

class JeandleIntrinsicLoweringHelper : public AllStatic {
 public:
  static bool is_double_constant(llvm::Value* value, double expected) {
    llvm::ConstantFP* constant = llvm::dyn_cast<llvm::ConstantFP>(value);
    if (constant == nullptr) {
      return false;
    }
    llvm::APFloat expected_value(expected);
    return constant->getValueAPF().bitwiseIsEqual(expected_value);
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
                                                              const JeandleRuntimeEntrypoint* entry) const {
  JeandleIntrinsicIRSemantics::annotate_instruction(inst, desc, decision.ir_plan, entry);
}

llvm::CallInst* JeandleIntrinsicLowering::emit_runtime_call(const JeandleIntrinsicDescriptor& desc,
                                                            const JeandleIntrinsicDecision& decision,
                                                            const JeandleRuntimeEntrypoint& entry,
                                                            llvm::ArrayRef<llvm::Value*> args) {
  llvm::SmallVector<llvm::OperandBundleDef, 1> bundles =
    JeandleIntrinsicIRSemantics::build_operand_bundles(_interp, decision.ir_plan);
  llvm::CallInst* call = _interp->create_call(entry.callee, args, entry.calling_conv, bundles);
  annotate_generated_instruction(*call, desc, decision, &entry);
  return call;
}

llvm::InvokeInst* JeandleIntrinsicLowering::emit_runtime_invoke(const JeandleIntrinsicDescriptor& desc,
                                                                const JeandleIntrinsicDecision& decision,
                                                                const JeandleRuntimeEntrypoint& entry,
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
  (void)target;
  switch (desc.semantics.category) {
    case JeandleIntrinsicCategory::PureMath:
      return lower_pure_math(desc, decision);
    case JeandleIntrinsicCategory::LibmMath:
      if (desc.id == vmIntrinsics::_dpow) {
        return lower_pow_hybrid(desc, decision);
      }
      return lower_libm_math(desc, decision);
    case JeandleIntrinsicCategory::MemorySemantic:
      if (desc.id == vmIntrinsics::_Reference_get) {
        return lower_reference_get(desc, decision);
      }
      if (desc.id == vmIntrinsics::_Reference_refersTo0) {
        return lower_reference_refers_to(desc, decision);
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
    case vmIntrinsics::_dsqrt:
    case vmIntrinsics::_dsqrt_strict:
      call = builder.CreateIntrinsic(JeandleType::java2llvm(T_DOUBLE, ctx), llvm::Intrinsic::sqrt,
                                     {_interp->_jvm->dpop()});
      annotate_generated_instruction(*call, desc, decision);
      _interp->_jvm->dpush(call);
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

  JeandleRuntimeEntrypoint entry;
  if (!JeandleRuntimeEntrypoints::resolve_math(desc.id, decision.impl_kind, _interp->_module, entry)) {
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
  if (JeandleIntrinsicLoweringHelper::is_double_constant(exp, 2.0)) {
    JeandleIntrinsicDecision refined = JeandleIntrinsicPolicy::refine(
      decision, desc, JeandleIntrinsicImplKind::IRInstruction, "pow(x,2) -> fmul");
    llvm::Value* fast = builder.CreateFMul(base, base);
    if (llvm::Instruction* inst = llvm::dyn_cast<llvm::Instruction>(fast)) {
      annotate_generated_instruction(*inst, desc, refined);
    }
    _interp->_jvm->dpush(fast);
    return true;
  }

  // Constant fast path: pow(x, 0.5) => llvm.sqrt(x).
  // This overrides the policy decision; refine() produces accurate metadata.
  if (JeandleIntrinsicLoweringHelper::is_double_constant(exp, 0.5)) {
    JeandleIntrinsicDecision refined = JeandleIntrinsicPolicy::refine(
      decision, desc, JeandleIntrinsicImplKind::LLVMBuiltinCall, "pow(x,0.5) -> llvm.sqrt");
    llvm::CallInst* fast = builder.CreateIntrinsic(JeandleType::java2llvm(T_DOUBLE, ctx), llvm::Intrinsic::sqrt, {base});
    annotate_generated_instruction(*fast, desc, refined);
    _interp->_jvm->dpush(fast);
    return true;
  }

  // General path: use the impl_kind that policy already resolved.
  // For LLVMBuiltinCall policy chose llvm.pow; for HotSpotStub/SharedRuntime delegate to runtime.
  if (decision.impl_kind == JeandleIntrinsicImplKind::LLVMBuiltinCall) {
    llvm::CallInst* call = builder.CreateIntrinsic(JeandleType::java2llvm(T_DOUBLE, ctx), llvm::Intrinsic::pow, {base, exp});
    annotate_generated_instruction(*call, desc, decision);
    _interp->_jvm->dpush(call);
    return true;
  }

  JeandleRuntimeEntrypoint entry;
  if (!JeandleRuntimeEntrypoints::resolve_math(vmIntrinsics::_dpow, decision.impl_kind, _interp->_module, entry)) {
    return false;
  }
  if (decision.ir_plan.needs_exception_edge) {
    _interp->_jvm->dpush(emit_runtime_invoke(desc, decision, entry, {base, exp}));
  } else {
    _interp->_jvm->dpush(emit_runtime_call(desc, decision, entry, {base, exp}));
  }
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
