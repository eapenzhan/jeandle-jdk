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

#include "jeandle/jeandleIntrinsicRegistry.hpp"

#include "jeandle/__hotspotHeadersBegin__.hpp"
#include "ci/ciMethod.hpp"

static constexpr JeandleTrapReasonMask trap_reason_mask(Deoptimization::DeoptReason reason) {
  return JeandleTrapReasonMask(1u) << static_cast<uint>(reason);
}

class JeandleIntrinsicRegistryTable : public AllStatic {
 public:
  static constexpr const JeandleIntrinsicDescriptor* table_begin() {
    return &_intrinsic_table[0];
  }

  static constexpr const JeandleIntrinsicDescriptor* table_end() {
    return &_intrinsic_table[ARRAY_SIZE(_intrinsic_table)];
  }

 private:
  static constexpr JeandleIntrinsicDescriptor _intrinsic_table[] = {
    { vmIntrinsics::_dabs,
      {JeandleIntrinsicCategory::PureMath, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },
    { vmIntrinsics::_fabs,
      {JeandleIntrinsicCategory::PureMath, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },
    { vmIntrinsics::_iabs,
      {JeandleIntrinsicCategory::PureMath, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },
    { vmIntrinsics::_labs,
      {JeandleIntrinsicCategory::PureMath, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },
    { vmIntrinsics::_bitCount_i,
      {JeandleIntrinsicCategory::PureMath, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },
    { vmIntrinsics::_bitCount_l,
      {JeandleIntrinsicCategory::PureMath, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },
    { vmIntrinsics::_dsqrt,
      {JeandleIntrinsicCategory::PureMath, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },
    { vmIntrinsics::_dsqrt_strict,
      {JeandleIntrinsicCategory::PureMath, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },

    // Rounding: GuardedHybrid because a native instruction is required for
    // correctness/performance (SSE4.1 ROUNDSD on x86, FRINT* on AArch64).
    // JeandleIntrinsicSupport::query() checks the CPU feature at decision time;
    // if absent, any_path() returns false and the call is not intrinsified
    // (NormalInvoke fallback).  This mirrors C2's match_rule_supported() guard.
    { vmIntrinsics::_floor,
      {JeandleIntrinsicCategory::PureMath, {false, false}, {false, false}},
      JeandleLoweringKind::GuardedHybrid, JeandleFallbackPolicy::NormalInvoke, false, true, nullptr },
    { vmIntrinsics::_ceil,
      {JeandleIntrinsicCategory::PureMath, {false, false}, {false, false}},
      JeandleLoweringKind::GuardedHybrid, JeandleFallbackPolicy::NormalInvoke, false, true, nullptr },
    { vmIntrinsics::_rint,
      {JeandleIntrinsicCategory::PureMath, {false, false}, {false, false}},
      JeandleLoweringKind::GuardedHybrid, JeandleFallbackPolicy::NormalInvoke, false, true, nullptr },

    { vmIntrinsics::_floatToRawIntBits,
      {JeandleIntrinsicCategory::TypeCoercion, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },
    { vmIntrinsics::_intBitsToFloat,
      {JeandleIntrinsicCategory::TypeCoercion, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },
    { vmIntrinsics::_doubleToRawLongBits,
      {JeandleIntrinsicCategory::TypeCoercion, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },
    { vmIntrinsics::_longBitsToDouble,
      {JeandleIntrinsicCategory::TypeCoercion, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, true, nullptr },

    { vmIntrinsics::_dsin,
      {JeandleIntrinsicCategory::LibmMath, {false, false}, {false, false}},
      JeandleLoweringKind::RuntimeLeafCall, JeandleFallbackPolicy::NormalInvoke, true, true, nullptr },
    { vmIntrinsics::_dcos,
      {JeandleIntrinsicCategory::LibmMath, {false, false}, {false, false}},
      JeandleLoweringKind::RuntimeLeafCall, JeandleFallbackPolicy::NormalInvoke, true, true, nullptr },
    { vmIntrinsics::_dtan,
      {JeandleIntrinsicCategory::LibmMath, {false, false}, {false, false}},
      JeandleLoweringKind::RuntimeLeafCall, JeandleFallbackPolicy::NormalInvoke, true, true, nullptr },
    { vmIntrinsics::_dlog,
      {JeandleIntrinsicCategory::LibmMath, {false, false}, {false, false}},
      JeandleLoweringKind::RuntimeLeafCall, JeandleFallbackPolicy::NormalInvoke, true, true, nullptr },
    { vmIntrinsics::_dlog10,
      {JeandleIntrinsicCategory::LibmMath, {false, false}, {false, false}},
      JeandleLoweringKind::RuntimeLeafCall, JeandleFallbackPolicy::NormalInvoke, true, true, nullptr },
    { vmIntrinsics::_dexp,
      {JeandleIntrinsicCategory::LibmMath, {false, false}, {false, false}},
      JeandleLoweringKind::RuntimeLeafCall, JeandleFallbackPolicy::NormalInvoke, true, true, nullptr },
    { vmIntrinsics::_dpow,
      {JeandleIntrinsicCategory::LibmMath, {false, false}, {false, false}},
      JeandleLoweringKind::GuardedHybrid, JeandleFallbackPolicy::RuntimeCall, true, true, nullptr },

    // System hints
    { vmIntrinsics::_onSpinWait,
      {JeandleIntrinsicCategory::MacroSemantic, {false, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, false, nullptr },

    // Preconditions.checkIndex(int index, int length, BiFunction exceptionFactory) -> int
    //
    // Emits a single unsigned comparison (ICMP_UGE) that covers both index < 0 and
    // index >= length in one check, then branches to a DeoptTrap on failure.
    // The BiFunction callback argument is popped and discarded in the fast path; if
    // the guard fires the interpreter re-executes the full method and invokes it.
    //
    // Control semantics:
    //   may_deopt = true  — out-of-bounds guard triggers uncommon_trap(Reason_range_check)
    //   needs_exception_edge = false — no Java exception path; failure goes to deopt only
    //
    // Memory semantics: none — pure arithmetic check, no heap access.
    //
    // C2 behaviour reference: library_call.cpp checks too_many_traps for both
    // Reason_intrinsic (length < 0) and Reason_range_check (index OOB); we
    // mirror the same site throttle via trap_throttle_mask.
    { vmIntrinsics::_Preconditions_checkIndex,
      {JeandleIntrinsicCategory::MacroSemantic, {true, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::DeoptTrap, false, false, nullptr,
      trap_reason_mask(Deoptimization::Reason_intrinsic) |
          trap_reason_mask(Deoptimization::Reason_range_check) },

    // Preconditions.checkIndex(long index, long length, BiFunction exceptionFactory) -> long
    //
    // Identical trap semantics to the int variant; only the value width differs.
    { vmIntrinsics::_Preconditions_checkLongIndex,
      {JeandleIntrinsicCategory::MacroSemantic, {true, false}, {false, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::DeoptTrap, false, false, nullptr,
      trap_reason_mask(Deoptimization::Reason_intrinsic) |
          trap_reason_mask(Deoptimization::Reason_range_check) },

    // Object.getClass(): loads the java.lang.Class mirror via the klass's OopHandle.
    // TypeSemantic + JavaOperation: the two-level load (klass → OopHandle → mirror)
    // is implemented as jeandle.get_class.
    //
    // Memory semantics:
    //   has_memory_effect = true  — three memory loads (object header, OopHandle ptr, mirror oop)
    //   needs_gc_state    = true  — the final load resolves a heap oop from OopStorage; a future
    //                               GC-aware pass must see this site for barrier insertion
    //
    // Control semantics:
    //   may_deopt              = false — NPE is an exception, not a deopt
    //   requires_nonnull_receiver = true — the null check is the caller's responsibility;
    //                               invokevirtual/invokeinterface bytecodes null-check the receiver
    //                               before dispatch.  If getClass is ever lowered via a non-invoke
    //                               path (e.g., inlined JavaOp, direct IR construction), a null
    //                               check must be added at that callsite or inside the JavaOp itself.
    //
    // Note: attach_deopt_bundle is still set to true unconditionally for JavaOpCall mode
    // (see make_plan); this is a conservative plan-level decision independent of may_deopt.
    { vmIntrinsics::_getClass,
      {JeandleIntrinsicCategory::TypeSemantic, {false, false, true}, {true, true}},
      JeandleLoweringKind::JavaOperation, JeandleFallbackPolicy::NormalInvoke, false, false, "jeandle.get_class" },

    // Reference.get(): returns the referent, applying a GC load barrier (WeakReferentLoad).
    // may_deopt = false — no speculative guard; attach_deopt_bundle is plan-driven by
    // needs_gc_state, not by deoptimization semantics.
    { vmIntrinsics::_Reference_get,
      {JeandleIntrinsicCategory::MemorySemantic, {false, false, true}, {true, true, JeandleMemoryBarrierKind::WeakReferentLoad}},
      JeandleLoweringKind::JavaOperation, JeandleFallbackPolicy::NormalInvoke, false, false, "jeandle.reference_get" },

    // Reference.refersTo0(): raw referent pointer identity comparison (no GC barrier).
    // may_deopt = false — no speculative guard.
    { vmIntrinsics::_Reference_refersTo0,
      {JeandleIntrinsicCategory::MemorySemantic, {false, false, true}, {true, true, JeandleMemoryBarrierKind::RawReferentRead}},
      JeandleLoweringKind::JavaOperation, JeandleFallbackPolicy::NormalInvoke, false, false, "jeandle.reference_refers_to" },

    // Memory fences: lower to LLVM fence instructions (acquire / release / seq_cst).
    // These have memory effects but no GC interaction; barrier_kind is None because
    // the fence IR instruction is the complete implementation — no GC pass augmentation needed.
    { vmIntrinsics::_loadFence,
      {JeandleIntrinsicCategory::BarrierSemantic, {false, false}, {true, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, false, nullptr },
    { vmIntrinsics::_storeFence,
      {JeandleIntrinsicCategory::BarrierSemantic, {false, false}, {true, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, false, nullptr },
    { vmIntrinsics::_fullFence,
      {JeandleIntrinsicCategory::BarrierSemantic, {false, false}, {true, false}},
      JeandleLoweringKind::PureIRNode, JeandleFallbackPolicy::None, false, false, nullptr },

    // PhantomReference.refersTo0 shares identical semantics with Reference.refersTo0:
    // raw referent read (no GC barrier), pointer identity comparison, boolean result.
    // may_deopt = false — no speculative guard.
    { vmIntrinsics::_PhantomReference_refersTo0,
      {JeandleIntrinsicCategory::MemorySemantic, {false, false, true}, {true, true, JeandleMemoryBarrierKind::RawReferentRead}},
      JeandleLoweringKind::JavaOperation, JeandleFallbackPolicy::NormalInvoke, false, false, "jeandle.reference_refers_to" },

    // StringCoding.countPositives(byte[] ba, int off, int len) → int
    //
    // Returns the number of leading bytes in ba[off..off+len) with bit 7 clear
    // (the positive-byte prefix length); returns len if all bytes are positive.
    //
    // Lowering: RuntimeLeafCall via a thin C++ scalar wrapper (count_positives_impl).
    // This establishes the ArrayScan/RuntimeLeafCall category path in the framework.
    //
    // TODO(simd-stub): replace wrapper with platform-native SIMD stubs once
    // standard-calling-convention variants are available:
    //   AArch64 — StubRoutines::aarch64::count_positives() (non-standard CC today)
    //   x86_64  — inline SSE/AVX2 via C2_MacroAssembler::count_positives
    //
    // Memory semantics:
    //   has_memory_effect = true  — reads the byte array slice
    //   needs_gc_state    = false — no GC barriers involved
    //
    // Control semantics:
    //   may_deopt = false — no speculative guard in the current scalar impl
    { vmIntrinsics::_countPositives,
      {JeandleIntrinsicCategory::ArrayScan, {false, false}, {true, false}},
      JeandleLoweringKind::RuntimeLeafCall, JeandleFallbackPolicy::NormalInvoke, true, false, nullptr,
      trap_reason_mask(Deoptimization::Reason_intrinsic) },
  };
};

constexpr JeandleIntrinsicDescriptor JeandleIntrinsicRegistryTable::_intrinsic_table[];

const JeandleIntrinsicDescriptor* JeandleIntrinsicRegistry::lookup(vmIntrinsics::ID id) {
  for (const JeandleIntrinsicDescriptor* it = JeandleIntrinsicRegistryTable::table_begin();
       it != JeandleIntrinsicRegistryTable::table_end();
       ++it) {
    if (it->id == id) {
      return it;
    }
  }
  return nullptr;
}

const JeandleIntrinsicDescriptor* JeandleIntrinsicRegistry::lookup(const ciMethod* method) {
  return method == nullptr ? nullptr : lookup(method->intrinsic_id());
}
