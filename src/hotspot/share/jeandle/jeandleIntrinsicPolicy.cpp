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

#include "jeandle/jeandleIntrinsicPolicy.hpp"
#include "jeandle/jeandleIntrinsicSupport.hpp"

#include "jeandle/__hotspotHeadersBegin__.hpp"
#include "ci/ciMethod.hpp"

class JeandleIntrinsicPolicyHelper : public AllStatic {
 public:
  static JeandleIRSemanticPlan make_plan(const JeandleIntrinsicDescriptor& desc,
                                         JeandleIntrinsicImplKind impl_kind) {
    JeandleIRSemanticPlan plan{};
    const JeandleControlSemantics& control = desc.semantics.control;
    const JeandleMemorySemantics& memory = desc.semantics.memory;

    if (impl_kind == JeandleIntrinsicImplKind::IRInstruction ||
        impl_kind == JeandleIntrinsicImplKind::LLVMBuiltinCall) {
      plan.mode = JeandleLoweringMode::PureLLVM;
    } else if (impl_kind == JeandleIntrinsicImplKind::HotSpotStub ||
               impl_kind == JeandleIntrinsicImplKind::SharedRuntime) {
      plan.mode = (memory.needs_gc_state || control.may_deopt) ?
        JeandleLoweringMode::ManagedRuntimeCall :
        JeandleLoweringMode::LeafRuntimeCall;
    } else if (impl_kind == JeandleIntrinsicImplKind::GuardedHybrid) {
      plan.mode = desc.supports_llvm_intrinsic ?
        JeandleLoweringMode::PureLLVM :
        JeandleLoweringMode::LeafRuntimeCall;
    } else {
      // JeandleIntrinsicImplKind::JavaOperation (and Unsupported fallback)
      plan.mode = JeandleLoweringMode::JavaOpCall;
    }

    // exception edge overrides only non-JavaOp paths; JavaOp invoke is handled
    // by emit_java_op_invoke which is selected in lowering based on needs_exception_edge
    if (control.needs_exception_edge && plan.mode != JeandleLoweringMode::JavaOpCall) {
      plan.mode = JeandleLoweringMode::ManagedRuntimeInvoke;
    }

    plan.attach_deopt_bundle = control.may_deopt || memory.needs_gc_state ||
                               plan.mode == JeandleLoweringMode::ManagedRuntimeCall ||
                               plan.mode == JeandleLoweringMode::ManagedRuntimeInvoke ||
                               plan.mode == JeandleLoweringMode::JavaOpCall;
    plan.attach_gc_leaf_attr = !memory.needs_gc_state &&
                               !memory.has_memory_effect &&
                               !control.may_deopt &&
                               !control.needs_exception_edge &&
                               (plan.mode == JeandleLoweringMode::LeafRuntimeCall ||
                                plan.mode == JeandleLoweringMode::PureLLVM);
    plan.needs_exception_edge = control.needs_exception_edge;
    return plan;
  }

  // Convenience: build a supported decision for the given impl_kind.
  static JeandleIntrinsicDecision make_decision(const JeandleIntrinsicDescriptor& desc,
                                                 JeandleIntrinsicImplKind kind,
                                                 const char* reason) {
    return {true, kind, make_plan(desc, kind), reason};
  }

  // Convenience: build an unsupported decision.
  static JeandleIntrinsicDecision unsupported(const JeandleIntrinsicDescriptor& desc,
                                               const char* reason) {
    return {false, JeandleIntrinsicImplKind::Unsupported,
            make_plan(desc, JeandleIntrinsicImplKind::Unsupported), reason};
  }
};

JeandleIntrinsicDecision JeandleIntrinsicPolicy::refine(const JeandleIntrinsicDecision& base,
                                                        const JeandleIntrinsicDescriptor& desc,
                                                        JeandleIntrinsicImplKind refined_kind,
                                                        const char* reason) {
  return {base.supported, refined_kind,
          JeandleIntrinsicPolicyHelper::make_plan(desc, refined_kind), reason};
}

JeandleIntrinsicDecision JeandleIntrinsicPolicy::decide(const JeandleIntrinsicDescriptor& desc,
                                                        const ciMethod* method) const {
  (void)method;

  switch (desc.lowering_kind) {
    case JeandleLoweringKind::PureIRNode: {
      // PureIRNode intrinsics are unconditionally supported; the impl_kind is
      // determined by category alone (no capability query needed).
      JeandleIntrinsicImplKind k;
      const char* reason;
      if (desc.semantics.category == JeandleIntrinsicCategory::TypeCoercion) {
        k = JeandleIntrinsicImplKind::IRInstruction;
        reason = "lower to IR instruction";
      } else {
        k = JeandleIntrinsicImplKind::LLVMBuiltinCall;
        reason = "lower to LLVM builtin";
      }
      return JeandleIntrinsicPolicyHelper::make_decision(desc, k, reason);
    }

    case JeandleLoweringKind::RuntimeLeafCall: {
      // Query capabilities once; apply preference rules.
      JeandleIntrinsicCapabilities caps = JeandleIntrinsicSupport::query(desc);
      if (!caps.any_path()) {
        return JeandleIntrinsicPolicyHelper::unsupported(desc, "no supported lowering");
      }
      if (caps.hotspot_preferred && caps.has_hotspot_stub) {
        return JeandleIntrinsicPolicyHelper::make_decision(
          desc, JeandleIntrinsicImplKind::HotSpotStub, "prefer HotSpot stub");
      }
      if (caps.hotspot_preferred && caps.has_shared_runtime) {
        return JeandleIntrinsicPolicyHelper::make_decision(
          desc, JeandleIntrinsicImplKind::SharedRuntime, "fallback to SharedRuntime");
      }
      if (caps.has_llvm_builtin) {
        return JeandleIntrinsicPolicyHelper::make_decision(
          desc, JeandleIntrinsicImplKind::LLVMBuiltinCall, "lower to LLVM builtin");
      }
      return JeandleIntrinsicPolicyHelper::unsupported(desc, "no supported lowering");
    }

    case JeandleLoweringKind::GuardedHybrid: {
      // Query capabilities once.  The general (non-constant-specialized) lowering
      // sub-kind is resolved here so that lower_*_hybrid() can switch on impl_kind
      // directly.  Constant fast paths (e.g. pow(x,2) -> fmul) are still chosen at
      // lowering time and call refine() to produce accurate per-instruction metadata.
      JeandleIntrinsicCapabilities caps = JeandleIntrinsicSupport::query(desc);
      if (!caps.any_path()) {
        return JeandleIntrinsicPolicyHelper::unsupported(desc, "no supported guarded lowering");
      }
      // Prefer LLVM builtin when HotSpot is disabled or no runtime path is available.
      if (caps.has_llvm_builtin && (!caps.hotspot_preferred || !caps.any_runtime())) {
        return JeandleIntrinsicPolicyHelper::make_decision(
          desc, JeandleIntrinsicImplKind::LLVMBuiltinCall,
          "GuardedHybrid: general path via LLVM builtin");
      }
      if (caps.has_hotspot_stub) {
        return JeandleIntrinsicPolicyHelper::make_decision(
          desc, JeandleIntrinsicImplKind::HotSpotStub,
          "GuardedHybrid: general path via HotSpot stub");
      }
      if (caps.has_shared_runtime) {
        return JeandleIntrinsicPolicyHelper::make_decision(
          desc, JeandleIntrinsicImplKind::SharedRuntime,
          "GuardedHybrid: general path via SharedRuntime");
      }
      // HotSpot preferred but no runtime available — fall back to LLVM builtin.
      if (caps.has_llvm_builtin) {
        return JeandleIntrinsicPolicyHelper::make_decision(
          desc, JeandleIntrinsicImplKind::LLVMBuiltinCall,
          "GuardedHybrid: LLVM builtin (no runtime path available)");
      }
      return JeandleIntrinsicPolicyHelper::unsupported(desc, "no supported guarded lowering");
    }

    case JeandleLoweringKind::JavaOperation:
      return {desc.java_op_name != nullptr, JeandleIntrinsicImplKind::JavaOperation,
              JeandleIntrinsicPolicyHelper::make_plan(desc, JeandleIntrinsicImplKind::JavaOperation),
              desc.java_op_name != nullptr ? "lower to JavaOp runtime glue" : "missing JavaOp"};
  }

  return JeandleIntrinsicPolicyHelper::unsupported(desc, "unhandled lowering kind");
}
