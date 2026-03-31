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

#include "jeandle/jeandleIntrinsicIRSemantics.hpp"

#include <string>

#include "jeandle/jeandleAbstractInterpreter.hpp"
#include "jeandle/jeandleRuntimeEntrypoints.hpp"

#include "jeandle/__hotspotHeadersBegin__.hpp"
#include "memory/allocation.hpp"

class JeandleIntrinsicIRSemanticNames : public AllStatic {
 public:
  static const char* lowering_mode_name(JeandleLoweringMode mode) {
    switch (mode) {
      case JeandleLoweringMode::PureLLVM:             return "pure-llvm";
      case JeandleLoweringMode::LeafRuntimeCall:      return "leaf-runtime-call";
      case JeandleLoweringMode::ManagedRuntimeCall:   return "managed-runtime-call";
      case JeandleLoweringMode::ManagedRuntimeInvoke: return "managed-runtime-invoke";
      case JeandleLoweringMode::JavaOpCall:           return "java-op-call";
    }
    return "unknown";
  }

  static const char* barrier_kind_name(JeandleMemoryBarrierKind kind) {
    switch (kind) {
      case JeandleMemoryBarrierKind::None:              return "none";
      case JeandleMemoryBarrierKind::WeakReferentLoad:  return "weak-referent-load";
      case JeandleMemoryBarrierKind::RawReferentRead:   return "raw-referent-read";
      case JeandleMemoryBarrierKind::CardMarkPost:      return "card-mark-post";
      case JeandleMemoryBarrierKind::VolatileLoad:      return "volatile-load";
      case JeandleMemoryBarrierKind::VolatileStore:     return "volatile-store";
    }
    return "unknown";
  }
};

// Attach a single-string metadata node to any instruction.
// Used for jeandle.* annotations so they do not contaminate the function
// attribute group (which would break tests expecting a solo "gc-leaf-function"
// attribute set).
static void set_str_metadata(llvm::Instruction& inst, llvm::StringRef key, llvm::StringRef value) {
  llvm::LLVMContext& ctx = inst.getContext();
  inst.setMetadata(key, llvm::MDNode::get(ctx, {llvm::MDString::get(ctx, value)}));
}

llvm::SmallVector<llvm::OperandBundleDef, 1>
JeandleIntrinsicIRSemantics::build_operand_bundles(JeandleAbstractInterpreter* interp,
                                                   const JeandleIRSemanticPlan& plan) {
  llvm::SmallVector<llvm::OperandBundleDef, 1> bundles;
  if (plan.attach_deopt_bundle) {
    bundles.push_back(interp->create_current_deopt_bundle());
  }
  return bundles;
}

void JeandleIntrinsicIRSemantics::annotate_instruction(llvm::Instruction& inst,
                                                       const JeandleIntrinsicDescriptor& desc,
                                                       const JeandleIRSemanticPlan& plan,
                                                       const JeandleRuntimeEntrypoint* entry) {
  // Jeandle semantic annotations go on the instruction as named metadata so
  // they are isolated from function-attribute groups (which affect code-gen).
  set_str_metadata(inst, "jeandle.intrinsic.id",
                   std::to_string(vmIntrinsics::as_int(desc.id)));
  set_str_metadata(inst, "jeandle.lowering.mode",
                   JeandleIntrinsicIRSemanticNames::lowering_mode_name(plan.mode));
  set_str_metadata(inst, "jeandle.semantic.barrier_kind",
                   JeandleIntrinsicIRSemanticNames::barrier_kind_name(desc.semantics.memory.barrier_kind));

  if (auto* call = llvm::dyn_cast<llvm::CallBase>(&inst)) {
    llvm::LLVMContext& ctx = inst.getContext();
    // gc-leaf-function must stay as a function attribute — it is consumed by
    // RewriteStatepointsForGC to skip statepoint insertion.
    if (plan.attach_gc_leaf_attr || (entry != nullptr && entry->is_gc_leaf)) {
      call->addFnAttr(llvm::Attribute::get(ctx, "gc-leaf-function"));
    }
    if (entry != nullptr && entry->well_known_name != nullptr) {
      set_str_metadata(inst, "jeandle.runtime.entry", entry->well_known_name);
    }
  }
}
