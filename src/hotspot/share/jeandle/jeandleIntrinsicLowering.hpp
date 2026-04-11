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
#include "jeandle/jeandleRuntimeEntrypoints.hpp"
#include "memory/allocation.hpp"

class JeandleAbstractInterpreter;
class ciMethod;

class JeandleIntrinsicLowering : public StackObj {
  JeandleAbstractInterpreter* _interp;

  bool lower_pure_math(const JeandleIntrinsicDescriptor& desc,
                       const JeandleIntrinsicDecision& decision);
  bool lower_type_coercion(const JeandleIntrinsicDescriptor& desc,
                            const JeandleIntrinsicDecision& decision);
  bool lower_libm_math(const JeandleIntrinsicDescriptor& desc,
                       const JeandleIntrinsicDecision& decision);
  bool lower_pow_hybrid(const JeandleIntrinsicDescriptor& desc,
                        const JeandleIntrinsicDecision& decision);
  bool lower_reference_get(const JeandleIntrinsicDescriptor& desc,
                           const JeandleIntrinsicDecision& decision);
  bool lower_reference_refers_to(const JeandleIntrinsicDescriptor& desc,
                                  const JeandleIntrinsicDecision& decision);
  bool lower_barrier_semantic(const JeandleIntrinsicDescriptor& desc,
                              const JeandleIntrinsicDecision& decision);
  bool lower_macro_semantic(const JeandleIntrinsicDescriptor& desc,
                            const JeandleIntrinsicDecision& decision);
  // Platform-specific spin-wait hint emission.
  // Implemented in cpu/<arch>/jeandleIntrinsicLowering_<arch>.cpp.
  bool lower_spin_wait_hint(const JeandleIntrinsicDescriptor& desc,
                            const JeandleIntrinsicDecision& decision);
  llvm::CallInst* emit_runtime_call(const JeandleIntrinsicDescriptor& desc,
                                    const JeandleIntrinsicDecision& decision,
                                    const JeandleRuntimeEntrypoint& entry,
                                    llvm::ArrayRef<llvm::Value*> args);
  llvm::InvokeInst* emit_runtime_invoke(const JeandleIntrinsicDescriptor& desc,
                                        const JeandleIntrinsicDecision& decision,
                                        const JeandleRuntimeEntrypoint& entry,
                                        llvm::ArrayRef<llvm::Value*> args);
  llvm::CallInst* emit_java_op_call(const JeandleIntrinsicDescriptor& desc,
                                    const JeandleIntrinsicDecision& decision,
                                    llvm::ArrayRef<llvm::Value*> args);
  llvm::InvokeInst* emit_java_op_invoke(const JeandleIntrinsicDescriptor& desc,
                                        const JeandleIntrinsicDecision& decision,
                                        llvm::ArrayRef<llvm::Value*> args);
  void annotate_generated_instruction(llvm::Instruction& inst,
                                      const JeandleIntrinsicDescriptor& desc,
                                      const JeandleIntrinsicDecision& decision,
                                      const JeandleRuntimeEntrypoint* entry = nullptr) const;

 public:
  explicit JeandleIntrinsicLowering(JeandleAbstractInterpreter* interp)
    : _interp(interp) {}

  bool lower(const JeandleIntrinsicDescriptor& desc,
             const JeandleIntrinsicDecision& decision,
             const ciMethod* target);
};

#endif // SHARE_JEANDLE_INTRINSIC_LOWERING_HPP
