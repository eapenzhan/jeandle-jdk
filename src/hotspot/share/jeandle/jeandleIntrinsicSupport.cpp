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

#include "jeandle/jeandleIntrinsicSupport.hpp"

#include "jeandle/jeandle_globals.hpp"

#include "jeandle/__hotspotHeadersBegin__.hpp"
#include "classfile/vmIntrinsics.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/stubRoutines.hpp"
#include "runtime/vm_version.hpp"

JeandleIntrinsicCapabilities JeandleIntrinsicSupport::query(const JeandleIntrinsicDescriptor& desc) {
  JeandleIntrinsicCapabilities caps{};

  caps.has_llvm_builtin   = desc.supports_llvm_intrinsic;
  caps.hotspot_preferred  = JeandleUseHotspotIntrinsics;

  // CPU-feature guards: some LLVM builtins require specific ISA extensions to
  // produce a native instruction.  Override has_llvm_builtin to false when the
  // required feature is absent so that policy falls back to NormalInvoke.
  //
  // _floor / _ceil / _rint:
  //   x86-64  — needs SSE4.1 (ROUNDSD).  Without it LLVM would synthesise a
  //             slow sequence; matching C2's Matcher::match_rule_supported()
  //             guard we simply decline to intrinsify.
  //   AArch64 — FRINTM/FRINTP/FRINTN are part of the ARMv8 base ISA; always ok.
  //   Other   — conservatively allow; LLVM will pick the best lowering.
  switch (desc.id) {
    case vmIntrinsics::_floor:
    case vmIntrinsics::_ceil:
    case vmIntrinsics::_rint:
#ifdef AMD64
      caps.has_llvm_builtin = VM_Version::supports_sse4_1();
#endif
      break;
    default:
      break;
  }

  if (!desc.supports_hotspot_stub) {
    return caps;
  }

  // Per-intrinsic stub and SharedRuntime availability.
  // has_hotspot_stub: the platform-specific stub has been installed.
  // has_shared_runtime: a SharedRuntime C-linkage function is available as a fallback.
  switch (desc.id) {
    case vmIntrinsics::_dsin:
      caps.has_hotspot_stub   = StubRoutines::dsin() != nullptr;
      caps.has_shared_runtime = CAST_FROM_FN_PTR(address, SharedRuntime::dsin) != nullptr;
      break;
    case vmIntrinsics::_dcos:
      caps.has_hotspot_stub   = StubRoutines::dcos() != nullptr;
      caps.has_shared_runtime = CAST_FROM_FN_PTR(address, SharedRuntime::dcos) != nullptr;
      break;
    case vmIntrinsics::_dtan:
      caps.has_hotspot_stub   = StubRoutines::dtan() != nullptr;
      caps.has_shared_runtime = CAST_FROM_FN_PTR(address, SharedRuntime::dtan) != nullptr;
      break;
    case vmIntrinsics::_dlog:
      caps.has_hotspot_stub   = StubRoutines::dlog() != nullptr;
      caps.has_shared_runtime = CAST_FROM_FN_PTR(address, SharedRuntime::dlog) != nullptr;
      break;
    case vmIntrinsics::_dlog10:
      caps.has_hotspot_stub   = StubRoutines::dlog10() != nullptr;
      caps.has_shared_runtime = CAST_FROM_FN_PTR(address, SharedRuntime::dlog10) != nullptr;
      break;
    case vmIntrinsics::_dexp:
      caps.has_hotspot_stub   = StubRoutines::dexp() != nullptr;
      caps.has_shared_runtime = CAST_FROM_FN_PTR(address, SharedRuntime::dexp) != nullptr;
      break;
    case vmIntrinsics::_dpow:
      caps.has_hotspot_stub   = StubRoutines::dpow() != nullptr;
      caps.has_shared_runtime = CAST_FROM_FN_PTR(address, SharedRuntime::dpow) != nullptr;
      break;
    // countPositives: our scalar C++ wrapper (count_positives_impl) is always
    // available on all platforms.  Set has_hotspot_stub so the RuntimeLeafCall
    // policy path chooses HotSpotStub and routes to lower_count_positives().
    // TODO(simd-stub): when platform-native stubs with standard calling conventions
    // become available, gate has_hotspot_stub on their runtime availability instead.
    case vmIntrinsics::_countPositives:
      caps.has_hotspot_stub = true;
      break;
    default:
      break;
  }

  return caps;
}
