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
 *
 */

#include "jeandle/__llvmHeadersBegin__.hpp"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/IntrinsicsAArch64.h"

#include "jeandle/jeandleAbstractInterpreter.hpp"
#include "jeandle/jeandleIntrinsicLowering.hpp"

bool JeandleIntrinsicLowering::lower_spin_wait_hint(
    const JeandleIntrinsicDescriptor& desc,
    const JeandleIntrinsicDecision& decision) {
  llvm::IRBuilder<>& builder = _interp->_ir_builder;
  // AArch64: YIELD instruction via llvm.aarch64.hint with hint value 1.
  // The hint encoding is defined in the ARMv8 architecture reference manual;
  // value 1 corresponds to YIELD, which signals the hardware that this thread
  // is in a spin-wait loop.
  llvm::CallInst* call = builder.CreateIntrinsic(
      llvm::Intrinsic::aarch64_hint, {}, {builder.getInt32(1)});
  annotate_generated_instruction(*call, desc, decision);
  // void return: nothing to push on the JVM operand stack
  return true;
}
