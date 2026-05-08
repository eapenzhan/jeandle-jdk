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

#ifdef ASSERT
static void validate_descriptor(const JeandleIntrinsicDescriptor& desc) {
  assert(desc.id != vmIntrinsics::_none && vmIntrinsics::is_valid_id(desc.id),
         "invalid Jeandle intrinsic id");
  assert(desc.lowering_kind != JeandleLoweringKind::PureIRNode ||
         !desc.needs_exception_edge(),
         "PureIRNode cannot require an exception edge");
  assert(desc.trap_throttle_mask == 0 || desc.may_deopt(),
         "trap throttling requires a deopt-capable intrinsic");
  assert(desc.lowering_kind != JeandleLoweringKind::JavaOperation || desc.java_op_name != nullptr,
         "JavaOperation descriptor must have a non-null java_op_name");
  assert(desc.java_op_name == nullptr || desc.java_op_name[0] != '\0',
         "empty JavaOp name string");
}
#endif

class JeandleIntrinsicRegistryTable : public AllStatic {
 public:
  static constexpr const JeandleIntrinsicDescriptor* table_begin() {
    return &_intrinsic_table[0];
  }

  static constexpr const JeandleIntrinsicDescriptor* table_end() {
    return &_intrinsic_table[ARRAY_SIZE(_intrinsic_table)];
  }

 private:
  // Descriptor fields, in order:
  //   id
  //   category
  //   control_flags  (bitmask of CTRL_*)
  //   memory_flags   (bitmask of MEM_*)
  //   barrier_kind
  //   lowering_kind
  //   support_flags  (bitmask of SUPPORT_*)
  //   java_op_name
  //   trap_throttle_mask
  //
  // Flag literals are self-describing at the call site, so the table reads as a
  // declarative list of facts about each intrinsic without consulting struct
  // definitions for what each bool position means.
  static constexpr JeandleIntrinsicDescriptor _intrinsic_table[] = {
    { vmIntrinsics::_dabs,                JeandleIntrinsicCategory::PureMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_fabs,                JeandleIntrinsicCategory::PureMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_iabs,                JeandleIntrinsicCategory::PureMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_labs,                JeandleIntrinsicCategory::PureMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_bitCount_i,          JeandleIntrinsicCategory::PureMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_bitCount_l,          JeandleIntrinsicCategory::PureMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_dsqrt,               JeandleIntrinsicCategory::PureMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_dsqrt_strict,        JeandleIntrinsicCategory::PureMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },

    // Rounding: GuardedHybrid because a native instruction is required for
    // correctness/performance (SSE4.1 ROUNDSD on x86, FRINT* on AArch64).
    // JeandleIntrinsicSupport::query() checks the CPU feature at decision time;
    // if absent, any_path() returns false and the call is not intrinsified.
    { vmIntrinsics::_floor,               JeandleIntrinsicCategory::PureMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::GuardedHybrid,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_ceil,                JeandleIntrinsicCategory::PureMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::GuardedHybrid,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_rint,                JeandleIntrinsicCategory::PureMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::GuardedHybrid,
      SUPPORT_LLVM_INTRIN,                nullptr },

    { vmIntrinsics::_floatToRawIntBits,   JeandleIntrinsicCategory::TypeCoercion,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_intBitsToFloat,      JeandleIntrinsicCategory::TypeCoercion,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_doubleToRawLongBits, JeandleIntrinsicCategory::TypeCoercion,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },
    { vmIntrinsics::_longBitsToDouble,    JeandleIntrinsicCategory::TypeCoercion,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_LLVM_INTRIN,                nullptr },

    { vmIntrinsics::_dsin,                JeandleIntrinsicCategory::LibmMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::RuntimeLeafCall,
      SUPPORT_HOTSPOT_STUB | SUPPORT_LLVM_INTRIN, nullptr },
    { vmIntrinsics::_dcos,                JeandleIntrinsicCategory::LibmMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::RuntimeLeafCall,
      SUPPORT_HOTSPOT_STUB | SUPPORT_LLVM_INTRIN, nullptr },
    { vmIntrinsics::_dtan,                JeandleIntrinsicCategory::LibmMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::RuntimeLeafCall,
      SUPPORT_HOTSPOT_STUB | SUPPORT_LLVM_INTRIN, nullptr },
    { vmIntrinsics::_dlog,                JeandleIntrinsicCategory::LibmMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::RuntimeLeafCall,
      SUPPORT_HOTSPOT_STUB | SUPPORT_LLVM_INTRIN, nullptr },
    { vmIntrinsics::_dlog10,              JeandleIntrinsicCategory::LibmMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::RuntimeLeafCall,
      SUPPORT_HOTSPOT_STUB | SUPPORT_LLVM_INTRIN, nullptr },
    { vmIntrinsics::_dexp,                JeandleIntrinsicCategory::LibmMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::RuntimeLeafCall,
      SUPPORT_HOTSPOT_STUB | SUPPORT_LLVM_INTRIN, nullptr },
    { vmIntrinsics::_dpow,                JeandleIntrinsicCategory::LibmMath,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::GuardedHybrid,
      SUPPORT_HOTSPOT_STUB | SUPPORT_LLVM_INTRIN, nullptr },

    // System hints
    { vmIntrinsics::_onSpinWait,          JeandleIntrinsicCategory::MacroSemantic,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_NONE,                       nullptr },

    // _blackhole: optimizer constraint — consume all arguments to prevent DCE, return void.
    // Uses volatile inline asm per argument so LLVM cannot eliminate the argument computations.
    // MacroSemantic + PureIRNode: always supported, no deopt, no memory effects.
    { vmIntrinsics::_blackhole,           JeandleIntrinsicCategory::MacroSemantic,
      CTRL_NONE,                          MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_NONE,                       nullptr },

    // Preconditions.checkIndex(int index, int length, BiFunction exceptionFactory) -> int
    //
    // Emits a single unsigned comparison (ICMP_UGE) that covers both index < 0 and
    // index >= length in one check, then branches to a DeoptTrap on failure.
    // The BiFunction callback argument is popped and discarded in the fast path; if
    // the guard fires the interpreter re-executes the full method and invokes it.
    //
    // C2 behaviour reference: library_call.cpp checks too_many_traps for both
    // Reason_intrinsic (length < 0) and Reason_range_check (index OOB); we
    // mirror the same site throttle via trap_throttle_mask.
    { vmIntrinsics::_Preconditions_checkIndex, JeandleIntrinsicCategory::MacroSemantic,
      CTRL_MAY_DEOPT,                     MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_NONE,                       nullptr,
      trap_reason_mask(Deoptimization::Reason_intrinsic) |
          trap_reason_mask(Deoptimization::Reason_range_check) },

    // Preconditions.checkIndex(long index, long length, BiFunction exceptionFactory) -> long
    // Identical trap semantics to the int variant; only the value width differs.
    { vmIntrinsics::_Preconditions_checkLongIndex, JeandleIntrinsicCategory::MacroSemantic,
      CTRL_MAY_DEOPT,                     MEM_NONE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_NONE,                       nullptr,
      trap_reason_mask(Deoptimization::Reason_intrinsic) |
          trap_reason_mask(Deoptimization::Reason_range_check) },

    // Object.getClass(): loads the java.lang.Class mirror via the klass's OopHandle.
    // TypeSemantic + JavaOperation: the two-level load (klass → OopHandle → mirror)
    // is implemented as jeandle.get_class.
    //
    // Memory: MEM_HAS_EFFECT | MEM_NEEDS_GC_STATE — three loads (header, OopHandle,
    // mirror oop); the mirror oop comes from OopStorage so a future GC-aware pass
    // must see this site for barrier insertion.
    //
    // Receiver null-check responsibility: invokevirtual/invokeinterface bytecodes
    // already null-check the receiver before dispatch, so this lowering path
    // assumes a non-null object on the stack.  If getClass is ever lowered via a
    // non-invoke path (inlined JavaOp, direct IR), a null check must be added at
    // that callsite or inside the JavaOp itself.
    //
    // Note: attach_deopt_bundle is still set unconditionally for JavaOpCall mode
    // (see make_plan); plan-level decision independent of CTRL_MAY_DEOPT.
    { vmIntrinsics::_getClass,            JeandleIntrinsicCategory::TypeSemantic,
      CTRL_NONE,                          MEM_HAS_EFFECT | MEM_NEEDS_GC_STATE,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::JavaOperation,
      SUPPORT_NONE,                       "jeandle.get_class" },

    // Reference.get(): returns the referent, applying a GC load barrier (WeakReferentLoad).
    // CTRL_NONE — no speculative guard; attach_deopt_bundle is plan-driven by
    // MEM_NEEDS_GC_STATE, not by deoptimization semantics.
    { vmIntrinsics::_Reference_get,       JeandleIntrinsicCategory::MemorySemantic,
      CTRL_NONE,                          MEM_HAS_EFFECT | MEM_NEEDS_GC_STATE,
      JeandleMemoryBarrierKind::WeakReferentLoad, JeandleLoweringKind::JavaOperation,
      SUPPORT_NONE,                       "jeandle.reference_get" },

    // Reference.refersTo0(): raw referent pointer identity comparison (no GC barrier).
    { vmIntrinsics::_Reference_refersTo0, JeandleIntrinsicCategory::MemorySemantic,
      CTRL_NONE,                          MEM_HAS_EFFECT | MEM_NEEDS_GC_STATE,
      JeandleMemoryBarrierKind::RawReferentRead, JeandleLoweringKind::JavaOperation,
      SUPPORT_NONE,                       "jeandle.reference_refers_to" },

    // Memory fences: lower to LLVM fence instructions (acquire / release / seq_cst).
    // MEM_HAS_EFFECT but no GC interaction; barrier_kind=None because the fence IR
    // instruction is the complete implementation — no GC pass augmentation needed.
    { vmIntrinsics::_loadFence,           JeandleIntrinsicCategory::BarrierSemantic,
      CTRL_NONE,                          MEM_HAS_EFFECT,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_NONE,                       nullptr },
    { vmIntrinsics::_storeFence,          JeandleIntrinsicCategory::BarrierSemantic,
      CTRL_NONE,                          MEM_HAS_EFFECT,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_NONE,                       nullptr },
    { vmIntrinsics::_fullFence,           JeandleIntrinsicCategory::BarrierSemantic,
      CTRL_NONE,                          MEM_HAS_EFFECT,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::PureIRNode,
      SUPPORT_NONE,                       nullptr },

    // PhantomReference.refersTo0 shares semantics with Reference.refersTo0:
    // raw referent read (no GC barrier), pointer identity comparison.
    { vmIntrinsics::_PhantomReference_refersTo0, JeandleIntrinsicCategory::MemorySemantic,
      CTRL_NONE,                          MEM_HAS_EFFECT | MEM_NEEDS_GC_STATE,
      JeandleMemoryBarrierKind::RawReferentRead, JeandleLoweringKind::JavaOperation,
      SUPPORT_NONE,                       "jeandle.reference_refers_to" },

    // Array.newInstance(Class<?> componentType, int length) → Object
    //
    // The JavaOp jeandle.new_array loads the cached array klass from the
    // component-type mirror and calls new_array on the fast path; if the klass is
    // not yet cached it falls back to Reflection::reflect_new_array.
    //
    // CTRL_NEEDS_EXCEPTION_EDGE: NegativeArraySizeException / NullPointerException /
    //   IllegalArgumentException may be thrown by the runtime.
    // MEM_HAS_EFFECT only (not MEM_NEEDS_GC_STATE): the runtime call handles
    //   allocation-time GC interaction, no per-lowering barrier required.
    { vmIntrinsics::_newArray,            JeandleIntrinsicCategory::AllocationSemantic,
      CTRL_NEEDS_EXCEPTION_EDGE,          MEM_HAS_EFFECT,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::JavaOperation,
      SUPPORT_NONE,                       "jeandle.new_array" },

    // StringCoding.countPositives(byte[] ba, int off, int len) → int
    //
    // Returns the number of leading bytes in ba[off..off+len) with bit 7 clear.
    // RuntimeLeafCall: at startup, generate_count_positives_adapter() installs a
    // platform-native SIMD stub adapter; if absent the entrypoint layer falls back
    // to the scalar count_positives_impl.
    //
    // CTRL_MAY_DEOPT: precondition guards (null, off<0, len<0, off+len>length)
    //   emit uncommon_trap(Reason_intrinsic) which requires a deopt bundle so the
    //   interpreter can re-execute and throw IOOBE.
    { vmIntrinsics::_countPositives,      JeandleIntrinsicCategory::ArrayScan,
      CTRL_MAY_DEOPT,                     MEM_HAS_EFFECT,
      JeandleMemoryBarrierKind::None,     JeandleLoweringKind::RuntimeLeafCall,
      SUPPORT_HOTSPOT_STUB,               nullptr,
      trap_reason_mask(Deoptimization::Reason_intrinsic) },
  };
};

constexpr JeandleIntrinsicDescriptor JeandleIntrinsicRegistryTable::_intrinsic_table[];

const JeandleIntrinsicDescriptor*
JeandleIntrinsicRegistry::_lookup[(int)vmIntrinsics::ID_LIMIT];

#ifdef ASSERT
bool JeandleIntrinsicRegistry::_initialized = false;
#endif

void JeandleIntrinsicRegistry::initialize() {
  // _lookup has static storage duration and is already zero-initialized (all nullptr)
  // by the C++ runtime before this function runs.  No explicit clear needed.

  for (const JeandleIntrinsicDescriptor* it = JeandleIntrinsicRegistryTable::table_begin();
       it != JeandleIntrinsicRegistryTable::table_end();
       ++it) {
    DEBUG_ONLY(validate_descriptor(*it);)
    const int index = vmIntrinsics::as_int(it->id);
    assert(_lookup[index] == nullptr, "duplicate Jeandle intrinsic descriptor");
    _lookup[index] = it;
  }

#ifdef ASSERT
  _initialized = true;
#endif
}

const JeandleIntrinsicDescriptor* JeandleIntrinsicRegistry::lookup(vmIntrinsics::ID id) {
  assert(_initialized, "JeandleIntrinsicRegistry must be initialized first");
  if (!vmIntrinsics::is_valid_id(id)) {
    return nullptr;
  }
  return _lookup[vmIntrinsics::as_int(id)];
}

const JeandleIntrinsicDescriptor* JeandleIntrinsicRegistry::lookup(const ciMethod* method) {
  return method == nullptr ? nullptr : lookup(method->intrinsic_id());
}
