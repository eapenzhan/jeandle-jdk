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
#include "ci/ciMethodData.hpp"
#include "runtime/deoptimization.hpp"

// Whether the chosen impl_kind crosses a runtime call boundary that the IR-level
// pipeline (statepoints, deopt bundles) must observe.
static bool is_managed_runtime_call(JeandleIntrinsicImplKind impl_kind,
                                    const JeandleIntrinsicDescriptor& desc) {
  if (impl_kind != JeandleIntrinsicImplKind::HotSpotStub &&
      impl_kind != JeandleIntrinsicImplKind::SharedRuntime) {
    return false;
  }
  return desc.needs_gc_state() || desc.may_deopt();
}

static JeandleIRSemanticPlan make_plan(const JeandleIntrinsicDescriptor& desc,
                                       JeandleIntrinsicImplKind impl_kind) {
  const bool is_javaop         = (impl_kind == JeandleIntrinsicImplKind::JavaOperation);
  const bool is_pure_llvm      = (impl_kind == JeandleIntrinsicImplKind::IRInstruction ||
                                  impl_kind == JeandleIntrinsicImplKind::LLVMBuiltinCall);
  const bool is_managed        = is_managed_runtime_call(impl_kind, desc);
  const bool is_leaf_call      = (impl_kind == JeandleIntrinsicImplKind::HotSpotStub ||
                                  impl_kind == JeandleIntrinsicImplKind::SharedRuntime) && !is_managed;
  const bool needs_unwind_edge = desc.needs_exception_edge() && !is_javaop;

  JeandleIRSemanticPlan plan{};

  // attach_deopt_bundle is required when:
  //   - the intrinsic itself can deopt;
  //   - the call site can safepoint: every safepoint is a potential deopt point,
  //     so it must carry interpreter state. RewriteStatepointsForGC does not need
  //     that state for its own work (GC root relocation); it merely threads the
  //     "deopt" bundle into the gc.statepoint's deopt section for HotSpot to use
  //     at runtime if the safepoint deopts.
  //   - the call crosses a managed-runtime boundary (call or invoke);
  //   - the call is a JavaOp (conservatively non-leaf until JavaOp infrastructure can
  //     derive precise bundle requirements).
  plan.attach_deopt_bundle = desc.may_deopt() || desc.needs_gc_state() ||
                             is_managed || needs_unwind_edge || is_javaop;

  // gc-leaf-function attribute is only correct on truly side-effect-free leaf paths:
  // pure LLVM IR or a leaf runtime call with no GC/exception/deopt interaction.
  plan.attach_gc_leaf_attr = !desc.needs_gc_state() &&
                             !desc.has_memory_effect() &&
                             !desc.may_deopt() &&
                             !desc.needs_exception_edge() &&
                             (is_pure_llvm || is_leaf_call);

  plan.needs_exception_edge = desc.needs_exception_edge();
  return plan;
}

static JeandleIntrinsicDecision make_decision(const JeandleIntrinsicDescriptor& desc,
                                              JeandleIntrinsicImplKind kind) {
  return {true, kind, make_plan(desc, kind)};
}

static JeandleIntrinsicDecision unsupported(const JeandleIntrinsicDescriptor& desc) {
  return {false, JeandleIntrinsicImplKind::Unsupported,
          make_plan(desc, JeandleIntrinsicImplKind::Unsupported)};
}

// Mirrors Compile::too_many_traps(caller_method, bci, reason):
//   1. per-BCI check: has_trap_at(bci, nullptr, reason) != 0 → true immediately
//   2. aggregate fallback: trap_count(reason) >= per_method_trap_limit(reason)
// Keyed on the CALLER method and invoke-site BCI, not the callee MDO, so one
// hot caller cannot disable the intrinsic for all other call sites.
// For non-speculate reasons (Reason_intrinsic, Reason_range_check) m = nullptr.
//
// Known gap vs C2: C2 also maintains a per-compilation trap count accumulator
// (Compile::_trap_count[]) that sums traps across the root method and all inlined
// callees in the same compilation unit. The fallback here only reads the caller
// method's own MDO, which is equivalent for single-method compilations but weaker
// when non-intrinsic inlining is introduced.
// TODO: add a per-compilation accumulator to JeandleAbstractInterpreter (or
// JeandleCompilation) once non-intrinsic inlining is supported.
static bool too_many_traps_at(const ciMethod* caller, int bci,
                              Deoptimization::DeoptReason reason) {
  if (caller == nullptr) return false;
  ciMethodData* md = const_cast<ciMethod*>(caller)->method_data();
  if (md == nullptr || md->is_empty()) return false;
  if (md->has_trap_at(bci, nullptr, reason) != 0) return true;
  return md->trap_count(reason) >= Deoptimization::per_method_trap_limit(reason);
}

static bool too_many_traps_for_any_reason(const ciMethod* caller, int bci,
                                          JeandleTrapReasonMask mask) {
  uint reason_index = 0;
  while (mask != 0) {
    if ((mask & 1u) != 0 &&
        too_many_traps_at(caller, bci,
                          static_cast<Deoptimization::DeoptReason>(reason_index))) {
      return true;
    }
    reason_index++;
    mask >>= 1;
  }
  return false;
}

// Pick the best available HotSpot runtime path, preferring the dedicated stub
// over the generic SharedRuntime entry.  Returns Unsupported if neither exists.
static JeandleIntrinsicImplKind try_hotspot_path(const JeandleIntrinsicCapabilities& caps) {
  if (caps.has_hotspot_stub)   return JeandleIntrinsicImplKind::HotSpotStub;
  if (caps.has_shared_runtime) return JeandleIntrinsicImplKind::SharedRuntime;
  return JeandleIntrinsicImplKind::Unsupported;
}

JeandleIntrinsicDecision JeandleIntrinsicPolicy::refine(const JeandleIntrinsicDecision& base,
                                                        const JeandleIntrinsicDescriptor& desc,
                                                        JeandleIntrinsicImplKind refined_kind) {
  return {base.supported, refined_kind, make_plan(desc, refined_kind)};
}

JeandleIntrinsicDecision JeandleIntrinsicPolicy::decide(const JeandleIntrinsicDescriptor& desc,
                                                        const ciMethod* caller,
                                                        int caller_bci) const {
  if (too_many_traps_for_any_reason(caller, caller_bci, desc.trap_throttle_mask)) {
    return unsupported(desc);
  }

  switch (desc.lowering_kind) {
    case JeandleLoweringKind::PureIRInstruction:
      // Bare LLVM IR instruction (bitcast, fence). Unconditionally supported,
      // no capability query needed.
      return make_decision(desc, JeandleIntrinsicImplKind::IRInstruction);

    case JeandleLoweringKind::PureLLVMBuiltin:
      // Named llvm.* builtin or platform-specific LLVM target intrinsic.
      // Unconditionally supported, no capability query needed.
      return make_decision(desc, JeandleIntrinsicImplKind::LLVMBuiltinCall);

    case JeandleLoweringKind::RuntimeLeafCall:
    case JeandleLoweringKind::GuardedHybrid: {
      // RuntimeLeafCall and GuardedHybrid share identical policy logic: a HotSpot
      // path wins only when it is preferred AND an actual runtime path exists,
      // otherwise the LLVM builtin. The two descriptor kinds differ only in the
      // lowering function body — a GuardedHybrid lowering (e.g. lower_pow_hybrid)
      // emits its own fast/slow guard, a RuntimeLeafCall lowering is a straight
      // call — which policy does not influence. The distinct names are kept as a
      // descriptor-level semantic label.
      JeandleIntrinsicCapabilities caps = JeandleIntrinsicSupport::query(desc);
      if (caps.hotspot_preferred && caps.any_runtime()) {
        JeandleIntrinsicImplKind k = try_hotspot_path(caps);
        if (k != JeandleIntrinsicImplKind::Unsupported) return make_decision(desc, k);
      }
      if (caps.has_llvm_builtin) return make_decision(desc, JeandleIntrinsicImplKind::LLVMBuiltinCall);
      return unsupported(desc);
    }

    case JeandleLoweringKind::JavaOperation:
      if (desc.java_op_name == nullptr) {
        return unsupported(desc);
      }
      return make_decision(desc, JeandleIntrinsicImplKind::JavaOperation);
  }

  return unsupported(desc);
}
