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
 */

#ifndef SHARE_JEANDLE_INTRINSIC_REGISTRY_HPP
#define SHARE_JEANDLE_INTRINSIC_REGISTRY_HPP

#include "jeandle/__hotspotHeadersBegin__.hpp"
#include "classfile/vmIntrinsics.hpp"
#include "memory/allocation.hpp"
#include "runtime/deoptimization.hpp"

class ciMethod;

// High-level semantic family used as the first lowering dispatch key.  Entries
// in the same category share a lowering shape; individual IDs are still handled
// by the category-specific lowering code.
enum class JeandleIntrinsicCategory {
  PureMath,            // arithmetic lowered to LLVM IR/builtins
  LibmMath,            // math calls that may use libm/HotSpot stubs
  TypeCoercion,        // bit-level reinterpretation between primitive types (bitcast)
  MemorySemantic,      // heap/reference operations with GC-visible semantics
  TypeSemantic,        // type/reflection operations
  AllocationSemantic,  // allocation operations that may throw
  BarrierSemantic,     // memory ordering and GC barrier semantics
  MacroSemantic,       // VM/compiler pseudo-intrinsics such as blackhole
  ArrayScan            // byte-array scan intrinsics (countPositives, etc.)
};

// Control-flow facts about an intrinsic.  Combined into descriptor.control_flags
// with bitwise OR.  Intentionally an unscoped enum so descriptors can write
// `CTRL_MAY_DEOPT | CTRL_NEEDS_EXCEPTION_EDGE` without operator overloads, and
// so unset entries can simply write CTRL_NONE.
enum JeandleControlFlag : uint8_t {
  CTRL_NONE                 = 0,
  // The intrinsic lowering can transfer control to uncommon_trap/deopt.
  CTRL_MAY_DEOPT            = 1u << 0,
  // The intrinsic may throw a Java exception from the lowered path and needs
  // invoke-style exception continuation handling, not just deopt replay.
  CTRL_NEEDS_EXCEPTION_EDGE = 1u << 1,
};

// Memory-effect facts about an intrinsic.  Combined into descriptor.memory_flags
// with bitwise OR.  barrier_kind is a separate descriptor field because it is a
// multi-valued enum, not a yes/no flag.
enum JeandleMemoryFlag : uint8_t {
  MEM_NONE              = 0,
  // The intrinsic reads/writes heap or otherwise constrains memory ordering.
  MEM_HAS_EFFECT        = 1u << 0,
  // The lowered IR/call must remain visible to GC-aware statepoint/barrier code.
  MEM_NEEDS_GC_STATE    = 1u << 1,
};

// What lowering paths a descriptor *declares* it can take.  Combined into
// descriptor.support_flags with bitwise OR.  Per-VM availability of those paths
// (stub installed, CPU feature present) is a runtime check in JeandleIntrinsicSupport.
enum JeandleSupportFlag : uint8_t {
  SUPPORT_NONE          = 0,
  // A HotSpot-generated stub or SharedRuntime fallback is an available impl.
  SUPPORT_HOTSPOT_STUB  = 1u << 0,
  // LLVM has a builtin or direct IR representation for this intrinsic.
  SUPPORT_LLVM_INTRIN   = 1u << 1,
};

enum class JeandleMemoryBarrierKind {
  None,
  WeakReferentLoad,  // Reference.get: GC-specific load barrier required
  RawReferentRead,   // Reference.refersTo0: intentional raw read, bypasses GC barrier
  CardMarkPost,      // post-write card table mark
  VolatileLoad,      // acquire semantics
  VolatileStore,     // release semantics
};

enum class JeandleLoweringKind {
  PureIRNode,      // lower directly to LLVM IR nodes without a call boundary
  RuntimeLeafCall, // emit a runtime/stub call that does not safepoint or throw
  GuardedHybrid,   // choose between IR/builtin and runtime paths by capability
  JavaOperation    // delegate complex semantics to a JavaOp runtime glue method
};

using JeandleTrapReasonMask = uint32_t;
static_assert(Deoptimization::Reason_LIMIT <= 32,
              "JeandleTrapReasonMask must be widened");

struct JeandleIntrinsicDescriptor {
  // VM intrinsic ID being described.  This is also the O(1) lookup-table key.
  vmIntrinsics::ID id;
  // High-level semantic family selected as the first lowering dispatch key.
  JeandleIntrinsicCategory category;
  // Bitmask of JeandleControlFlag.
  uint8_t control_flags;
  // Bitmask of JeandleMemoryFlag.
  uint8_t memory_flags;
  // GC barrier shape required by the intrinsic, if any.
  JeandleMemoryBarrierKind barrier_kind;
  // Coarse lowering family selected before capability/fallback refinement.
  JeandleLoweringKind lowering_kind;
  // Bitmask of JeandleSupportFlag declaring which lowering paths exist.
  uint8_t support_flags;
  // JavaOp symbol used only by JavaOperation descriptors; nullptr otherwise.
  const char* java_op_name;
  // Deoptimization reasons that throttle admission when too many traps occurred
  // at the invoke site.  Zero means no trap-based throttling.
  JeandleTrapReasonMask trap_throttle_mask;

  // Inline accessors so consumers can read named flags without bit-twiddling.
  bool may_deopt()             const { return (control_flags & CTRL_MAY_DEOPT) != 0; }
  bool needs_exception_edge()  const { return (control_flags & CTRL_NEEDS_EXCEPTION_EDGE) != 0; }
  bool has_memory_effect()     const { return (memory_flags  & MEM_HAS_EFFECT) != 0; }
  bool needs_gc_state()        const { return (memory_flags  & MEM_NEEDS_GC_STATE) != 0; }
  bool supports_hotspot_stub() const { return (support_flags & SUPPORT_HOTSPOT_STUB) != 0; }
  bool supports_llvm_intrin()  const { return (support_flags & SUPPORT_LLVM_INTRIN) != 0; }
};

class JeandleIntrinsicRegistry : public AllStatic {
 private:
  static const JeandleIntrinsicDescriptor* _lookup[(int)vmIntrinsics::ID_LIMIT];
#ifdef ASSERT
  static bool _initialized;
#endif

 public:
  static void initialize();
  static const JeandleIntrinsicDescriptor* lookup(vmIntrinsics::ID id);
  static const JeandleIntrinsicDescriptor* lookup(const ciMethod* method);
};

#endif // SHARE_JEANDLE_INTRINSIC_REGISTRY_HPP
