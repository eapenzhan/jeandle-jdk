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

enum class JeandleIntrinsicCategory {
  PureMath,
  LibmMath,
  TypeCoercion,   // bit-level reinterpretation between primitive types (bitcast)
  MemorySemantic,
  TypeSemantic,
  AllocationSemantic,
  BarrierSemantic,
  MacroSemantic,
  ArrayScan       // byte-array scan intrinsics (countPositives, etc.)
};

struct JeandleControlSemantics {
  bool may_deopt;
  bool needs_exception_edge;
  // Set true when the intrinsic lowering assumes the receiver is already non-null
  // (i.e., the null check is the caller's responsibility, not this intrinsic's).
  // This is true for all invokevirtual/invokeinterface JavaOps where the abstract
  // interpreter has already performed the null check before dispatch.
  bool requires_nonnull_receiver = false;
};

enum class JeandleMemoryBarrierKind {
  None,
  WeakReferentLoad,  // Reference.get: GC-specific load barrier required
  RawReferentRead,   // Reference.refersTo0: intentional raw read, bypasses GC barrier
  CardMarkPost,      // post-write card table mark
  VolatileLoad,      // acquire semantics
  VolatileStore,     // release semantics
};

struct JeandleMemorySemantics {
  bool has_memory_effect;
  bool needs_gc_state;
  JeandleMemoryBarrierKind barrier_kind = JeandleMemoryBarrierKind::None;
};

struct JeandleIntrinsicSemantics {
  JeandleIntrinsicCategory category;
  JeandleControlSemantics control;
  JeandleMemorySemantics memory;
};

enum class JeandleLoweringKind {
  PureIRNode,
  RuntimeLeafCall,
  GuardedHybrid,
  JavaOperation
};

enum class JeandleFallbackPolicy {
  None,           // fallback is unreachable; the preferred lowering always succeeds
  NormalInvoke,   // intrinsic not selected; caller keeps the original Java invoke
  RuntimeCall,    // guarded intrinsic; slow path calls a runtime helper
  JavaOperation,  // guarded intrinsic; slow path is a JavaOp-based runtime operation
  DeoptTrap,      // guarded intrinsic; failure path deoptimizes (no runtime call)
  ExactResult     // guarded intrinsic; guard failure produces a known constant result
};

using JeandleTrapReasonMask = uint32_t;
static_assert(Deoptimization::Reason_LIMIT <= 32,
              "JeandleTrapReasonMask must be widened");

struct JeandleIntrinsicDescriptor {
  vmIntrinsics::ID id;
  JeandleIntrinsicSemantics semantics;
  JeandleLoweringKind lowering_kind;
  JeandleFallbackPolicy fallback_policy;
  bool supports_hotspot_stub;
  bool supports_llvm_intrinsic;
  const char* java_op_name;
  JeandleTrapReasonMask trap_throttle_mask = 0;
};

class JeandleIntrinsicRegistry : public AllStatic {
 public:
  static const JeandleIntrinsicDescriptor* lookup(vmIntrinsics::ID id);
  static const JeandleIntrinsicDescriptor* lookup(const ciMethod* method);
};

#endif // SHARE_JEANDLE_INTRINSIC_REGISTRY_HPP
