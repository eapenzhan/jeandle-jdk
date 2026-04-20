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

#ifndef SHARE_JEANDLE_INTRINSIC_POLICY_HPP
#define SHARE_JEANDLE_INTRINSIC_POLICY_HPP

#include "jeandle/jeandleIntrinsicRegistry.hpp"
#include "jeandle/jeandleIntrinsicSupport.hpp"
#include "memory/allocation.hpp"

class ciMethod;

enum class JeandleIntrinsicImplKind {
  Unsupported,
  // PureIRNode sub-kinds: inline into the current function's IR, no call boundary
  IRInstruction,    // bare LLVM IR instruction: bitcast, fmul, icmp, etc.
  LLVMBuiltinCall,  // call to a named llvm.* builtin or platform-specific LLVM target intrinsic
                    // (e.g. llvm.fabs, llvm.ctpop, llvm.x86.sse2.pause, llvm.aarch64.hint)
  // Non-PureIRNode kinds: cross call boundaries or delegate to the runtime
  HotSpotStub,
  SharedRuntime,
  GuardedHybrid,
  JavaOperation
};

enum class JeandleLoweringMode {
  PureLLVM,
  LeafRuntimeCall,
  ManagedRuntimeCall,
  ManagedRuntimeInvoke,
  JavaOpCall
};

struct JeandleIRSemanticPlan {
  JeandleLoweringMode mode;
  bool attach_deopt_bundle;
  bool attach_gc_leaf_attr;
  bool needs_exception_edge;
};

struct JeandleIntrinsicDecision {
  bool supported;
  JeandleIntrinsicImplKind impl_kind;
  JeandleIRSemanticPlan ir_plan;
  const char* reason;
};

class JeandleIntrinsicPolicy : public StackObj {
 public:
  JeandleIntrinsicDecision decide(const JeandleIntrinsicDescriptor& desc,
                                  const ciMethod* caller,
                                  int caller_bci) const;

  // Refine a GuardedHybrid decision to the specific impl_kind chosen at
  // lowering time.  The caller passes the actual sub-path that was selected
  // (e.g. IRInstruction, LLVMBuiltinCall, HotSpotStub, SharedRuntime) so that
  // impl_kind and ir_plan accurately reflect the instruction being emitted.
  static JeandleIntrinsicDecision refine(const JeandleIntrinsicDecision& base,
                                         const JeandleIntrinsicDescriptor& desc,
                                         JeandleIntrinsicImplKind refined_kind,
                                         const char* reason);
};

#endif // SHARE_JEANDLE_INTRINSIC_POLICY_HPP
