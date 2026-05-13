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

#ifndef SHARE_JEANDLE_INTRINSIC_IR_SEMANTICS_HPP
#define SHARE_JEANDLE_INTRINSIC_IR_SEMANTICS_HPP

#include "jeandle/__llvmHeadersBegin__.hpp"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Value.h"

#include "jeandle/jeandleIntrinsicPolicy.hpp"

class JeandleAbstractInterpreter;

struct JeandleIntrinsicEntrypoint;

// Translates an intrinsic decision into LLVM IR-level facts: operand bundles,
// call attributes, and metadata.  This is its own layer in the framework,
// peer to Policy and Lowering rather than a continuation of Policy:
//
//   Policy answers "which impl_kind should we use here".
//   IRSemantics answers "given that impl_kind, what IR-level facts must be
//   attached so downstream LLVM passes behave correctly and so the lowering
//   contract is observable in IR dumps".
//   Lowering answers "now emit the actual instructions".
//
// IRSemantics evolves on its own axis: new GC-aware metadata, new alias/
// noalias attributes, new keys synchronised with jeandle-llvm passes — all
// land here without touching Policy or the descriptor.  It depends on the
// LLVM headers and on AbstractInterpreter; Policy stays ciMethod-only.
//
// Two kinds of facts are attached to the emitted IR here:
//
//   1. Behavioural contracts consumed by LLVM passes today.
//      - The "gc-leaf-function" function attribute is read by
//        RewriteStatepointsForGC to skip statepoint insertion on leaf calls.
//      - The "deopt" operand bundle (built by build_operand_bundles) feeds the
//        same pass with the interpreter state needed to materialise deopts.
//
//   2. Observability labels reserved as a forward contract for GC-aware /
//      barrier-aware LLVM passes that have not yet been written:
//        jeandle.intrinsic.id, jeandle.lowering.mode,
//        jeandle.semantic.barrier_kind, jeandle.runtime.entry.
//      These have no LLVM-side consumer today; they appear in IR dumps and
//      serve as a stable place for a future pass (e.g. one that reads
//      barrier_kind to emit collector-specific barriers) to plug in without
//      re-threading the descriptor through the lowering layer.  Treat them as
//      part of the IR contract: keep the strings stable, do not relocate.
class JeandleIntrinsicIRSemantics : public AllStatic {
 public:
  static llvm::SmallVector<llvm::OperandBundleDef, 1> build_operand_bundles(JeandleAbstractInterpreter* interp,
                                                                             const JeandleIRSemanticPlan& plan);
  static void annotate_instruction(llvm::Instruction& inst,
                                   const JeandleIntrinsicDescriptor& desc,
                                   const JeandleIntrinsicDecision& decision,
                                   const JeandleIntrinsicEntrypoint* entry = nullptr);
};

#endif // SHARE_JEANDLE_INTRINSIC_IR_SEMANTICS_HPP
