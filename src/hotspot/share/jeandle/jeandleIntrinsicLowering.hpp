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

#ifndef SHARE_JEANDLE_INTRINSIC_LOWERING_HPP
#define SHARE_JEANDLE_INTRINSIC_LOWERING_HPP

#include "jeandle/__llvmHeadersBegin__.hpp"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"

#include "jeandle/jeandleIntrinsicPolicy.hpp"
#include "jeandle/jeandleIntrinsicEntrypoints.hpp"
#include "memory/allocation.hpp"

class JeandleAbstractInterpreter;
class ciMethod;

class JeandleIntrinsicLowering : public StackObj {
  JeandleAbstractInterpreter* _interp;
  const ciMethod* _target;

  bool lower_pure_math(const JeandleIntrinsicDescriptor& desc,
                       const JeandleIntrinsicDecision& decision);
  bool lower_type_coercion(const JeandleIntrinsicDescriptor& desc,
                            const JeandleIntrinsicDecision& decision);
  bool lower_libm_math(const JeandleIntrinsicDescriptor& desc,
                       const JeandleIntrinsicDecision& decision);
  bool lower_pow_hybrid(const JeandleIntrinsicDescriptor& desc,
                        const JeandleIntrinsicDecision& decision);
  bool lower_get_class(const JeandleIntrinsicDescriptor& desc,
                       const JeandleIntrinsicDecision& decision);
  bool lower_reference_get(const JeandleIntrinsicDescriptor& desc,
                           const JeandleIntrinsicDecision& decision);
  bool lower_reference_refers_to(const JeandleIntrinsicDescriptor& desc,
                                  const JeandleIntrinsicDecision& decision);
  bool lower_barrier_semantic(const JeandleIntrinsicDescriptor& desc,
                              const JeandleIntrinsicDecision& decision);
  bool lower_preconditions_check_index(const JeandleIntrinsicDescriptor& desc,
                                       const JeandleIntrinsicDecision& decision);
  bool lower_count_positives(const JeandleIntrinsicDescriptor& desc,
                             const JeandleIntrinsicDecision& decision);
  bool lower_new_array(const JeandleIntrinsicDescriptor& desc,
                       const JeandleIntrinsicDecision& decision);
  bool lower_blackhole(const JeandleIntrinsicDescriptor& desc,
                       const JeandleIntrinsicDecision& decision);
  // Platform-specific spin-wait hint emission.
  // Implemented in cpu/<arch>/jeandleIntrinsicLowering_<arch>.cpp.
  bool lower_spin_wait_hint(const JeandleIntrinsicDescriptor& desc,
                            const JeandleIntrinsicDecision& decision);
  // Shared call-site skeleton for runtime stubs and JavaOps: builds the deopt
  // bundle, emits a call or an invoke (call path marked nounwind) based on
  // decision.ir_plan.needs_exception_edge, then runs the common IR annotations.
  // entry is optional runtime-stub metadata (nullptr for JavaOps).
  llvm::CallBase* emit_callsite(const JeandleIntrinsicDescriptor& desc,
                                const JeandleIntrinsicDecision& decision,
                                llvm::FunctionCallee callee,
                                llvm::CallingConv::ID calling_conv,
                                llvm::ArrayRef<llvm::Value*> args,
                                const JeandleIntrinsicEntrypoint* entry = nullptr);
  // Runtime-stub call site. Thin facade over emit_callsite.
  llvm::CallBase* emit_runtime_call(const JeandleIntrinsicDescriptor& desc,
                                    const JeandleIntrinsicDecision& decision,
                                    const JeandleIntrinsicEntrypoint& entry,
                                    llvm::ArrayRef<llvm::Value*> args);
  // JavaOp call site. Thin facade over emit_callsite; additionally tags the site
  // with the "jeandle.java_op" attribute.
  llvm::CallBase* emit_java_op_call(const JeandleIntrinsicDescriptor& desc,
                                    const JeandleIntrinsicDecision& decision,
                                    llvm::ArrayRef<llvm::Value*> args);
  void annotate_generated_instruction(llvm::Instruction& inst,
                                      const JeandleIntrinsicDescriptor& desc,
                                      const JeandleIntrinsicDecision& decision,
                                      const JeandleIntrinsicEntrypoint* entry = nullptr) const;
  void attach_callee_return_klass_attr(llvm::CallBase* call) const;

 public:
  explicit JeandleIntrinsicLowering(JeandleAbstractInterpreter* interp)
    : _interp(interp), _target(nullptr) {}

  bool lower(const JeandleIntrinsicDescriptor& desc,
             const JeandleIntrinsicDecision& decision,
             const ciMethod* target);
};

#endif // SHARE_JEANDLE_INTRINSIC_LOWERING_HPP
