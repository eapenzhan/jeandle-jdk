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

#ifndef SHARE_JEANDLE_RUNTIME_ENTRYPOINTS_HPP
#define SHARE_JEANDLE_RUNTIME_ENTRYPOINTS_HPP

#include "jeandle/__llvmHeadersBegin__.hpp"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Module.h"

#include "jeandle/jeandleIntrinsicPolicy.hpp"

#include "jeandle/__hotspotHeadersBegin__.hpp"
#include "classfile/vmIntrinsics.hpp"
#include "memory/allocation.hpp"

struct JeandleRuntimeEntrypoint {
  llvm::FunctionCallee callee;
  llvm::CallingConv::ID calling_conv;
  bool is_gc_leaf;
  const char* well_known_name;
};

class JeandleRuntimeEntrypoints : public AllStatic {
 public:
  static bool resolve_math(vmIntrinsics::ID id,
                           JeandleIntrinsicImplKind impl_kind,
                           llvm::Module& module,
                           JeandleRuntimeEntrypoint& out);
};

#endif // SHARE_JEANDLE_RUNTIME_ENTRYPOINTS_HPP
