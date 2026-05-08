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

#ifndef SHARE_JEANDLE_INTRINSIC_SUPPORT_HPP
#define SHARE_JEANDLE_INTRINSIC_SUPPORT_HPP

#include "jeandle/jeandleIntrinsicRegistry.hpp"

// Per-intrinsic capability snapshot, computed once at decision time.
//
// This is the Jeandle analog of C2Compiler::is_intrinsic_supported: a pure
// capability query that answers what lowering paths are actually available for
// a given descriptor at runtime (stub installed?  CPU feature present?  flag
// enabled?), separate from the policy that ranks those paths.
//
// The split is intentional and addresses three different kinds of facts:
//   descriptor           - what we declared statically about the intrinsic
//   capabilities (here)  - what is available right now in this VM
//   decision (Policy)    - which path we actually picked, given priorities
struct JeandleIntrinsicCapabilities {
  // Descriptor says supports_llvm_intrinsic; lowering can emit an llvm.* builtin call.
  bool has_llvm_builtin;
  // Descriptor says supports_hotspot_stub AND the per-intrinsic stub has been installed.
  bool has_hotspot_stub;
  // Descriptor says supports_hotspot_stub AND a SharedRuntime fallback function exists.
  bool has_shared_runtime;
  // JeandleUseHotspotIntrinsics flag: when true, HotSpot runtime paths are preferred over LLVM.
  bool hotspot_preferred;

  bool any_runtime() const { return has_hotspot_stub || has_shared_runtime; }
  bool any_path()    const { return has_llvm_builtin || any_runtime(); }
};

class JeandleIntrinsicSupport : public AllStatic {
 public:
  // Return the set of available lowering paths for the given descriptor.
  // All stub-installation, CPU-feature, and flag checks live in this single
  // method; callers receive a plain capability struct and apply their own
  // priority rules.
  static JeandleIntrinsicCapabilities query(const JeandleIntrinsicDescriptor& desc);
};

#endif // SHARE_JEANDLE_INTRINSIC_SUPPORT_HPP
