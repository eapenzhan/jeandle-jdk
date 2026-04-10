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

    // Reference.get(): returns the referent, applying a GC load barrier (WeakReferentLoad).
    // may_deopt = false — no speculative guard; attach_deopt_bundle is plan-driven by
    // needs_gc_state, not by deoptimization semantics.
    { vmIntrinsics::_Reference_get,
      {JeandleIntrinsicCategory::MemorySemantic, {false, false}, {true, true, JeandleMemoryBarrierKind::WeakReferentLoad}},
      JeandleLoweringKind::JavaOperation, JeandleFallbackPolicy::NormalInvoke, false, false, "jeandle.reference_get" },

    // Reference.refersTo0(): raw referent pointer identity comparison (no GC barrier).
    // may_deopt = false — no speculative guard.
    { vmIntrinsics::_Reference_refersTo0,
      {JeandleIntrinsicCategory::MemorySemantic, {false, false}, {true, true, JeandleMemoryBarrierKind::RawReferentRead}},
      JeandleLoweringKind::JavaOperation, JeandleFallbackPolicy::NormalInvoke, false, false, "jeandle.reference_refers_to" },
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
