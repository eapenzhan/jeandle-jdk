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
#include "llvm/IR/IntrinsicsX86.h"

#include "jeandle/jeandleAbstractInterpreter.hpp"
#include "jeandle/jeandleIntrinsicLowering.hpp"

bool JeandleIntrinsicLowering::lower_spin_wait_hint(
    const JeandleIntrinsicDescriptor& desc,
    const JeandleIntrinsicDecision& decision) {
  llvm::IRBuilder<>& builder = _interp->_ir_builder;
  // x86-64: PAUSE instruction — spin-wait hint that improves performance
  // and reduces power consumption in busy-wait loops.
  llvm::CallInst* call = builder.CreateIntrinsic(
      llvm::Intrinsic::x86_sse2_pause, llvm::ArrayRef<llvm::Type*>{}, {});
  annotate_generated_instruction(*call, desc, decision);
  // void return: nothing to push on the JVM operand stack
  return true;
}
