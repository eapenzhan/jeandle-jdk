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
#include "jeandle/jeandleRuntimeRoutine.hpp"

#include "jeandle/__hotspotHeadersBegin__.hpp"
#include "classfile/vmIntrinsics.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/stubRoutines.hpp"
#include "runtime/vm_version.hpp"

// CPU-feature guards: some LLVM builtins require specific ISA extensions to
// produce a native instruction.  When the required feature is absent we
// return false so policy falls back to NormalInvoke.
//
// _floor / _ceil / _rint:
//   x86-64  — needs SSE4.1 (ROUNDSD).  Without it LLVM would synthesise a slow
//             sequence; matching C2's Matcher::match_rule_supported() we simply
//             decline to intrinsify.
//   AArch64 — FRINTM/FRINTP/FRINTN are part of the ARMv8 base ISA; always ok.
//   Other   — conservatively allow; LLVM will pick the best lowering.
static bool cpu_supports_llvm_builtin(vmIntrinsics::ID id) {
  switch (id) {
    case vmIntrinsics::_floor:
    case vmIntrinsics::_ceil:
    case vmIntrinsics::_rint:
#ifdef AMD64
      return VM_Version::supports_sse4_1();
#else
      return true;
#endif
    default:
      return true;
  }
}

// Per-intrinsic stub and SharedRuntime availability probe.
//   has_hotspot_stub   — the platform-specific stub has been installed.
//   has_shared_runtime — a SharedRuntime C-linkage function is available as fallback.
// The libm family (dsin/dcos/.../dpow) all share the same probe shape; the
// LIBM_PROBE macro keeps each case to one line.  Intrinsics whose stub/runtime
// shape differs (e.g. countPositives) get their own explicit case below.
static void probe_hotspot_stubs(vmIntrinsics::ID id, JeandleIntrinsicCapabilities& caps) {
#define LIBM_PROBE(name)                                                                   \
  case vmIntrinsics::_##name:                                                              \
    caps.has_hotspot_stub   = StubRoutines::name() != nullptr;                             \
    caps.has_shared_runtime = CAST_FROM_FN_PTR(address, SharedRuntime::name) != nullptr;   \
    break;

  switch (id) {
    LIBM_PROBE(dsin)
    LIBM_PROBE(dcos)
    LIBM_PROBE(dtan)
    LIBM_PROBE(dlog)
    LIBM_PROBE(dlog10)
    LIBM_PROBE(dexp)
    LIBM_PROBE(dpow)
    // countPositives: has_hotspot_stub is true when the platform SIMD adapter has been
    // generated (AArch64: MacroAssembler::count_positives; x86: c2_MacroAssembler::count_positives).
    // has_shared_runtime is always true because the scalar C++ fallback (count_positives_impl)
    // is unconditionally available.
    case vmIntrinsics::_countPositives:
      caps.has_hotspot_stub   = JeandleRuntimeRoutine::count_positives_stub_adapter() != nullptr;
      caps.has_shared_runtime = true;
      break;
    default:
      break;
  }
#undef LIBM_PROBE
}

JeandleIntrinsicCapabilities JeandleIntrinsicSupport::query(const JeandleIntrinsicDescriptor& desc) {
  JeandleIntrinsicCapabilities caps{};
  caps.has_llvm_builtin  = desc.supports_llvm_intrin() && cpu_supports_llvm_builtin(desc.id);
  caps.hotspot_preferred = JeandleUseHotspotIntrinsics;
  if (desc.supports_hotspot_stub()) {
    probe_hotspot_stubs(desc.id, caps);
  }
  return caps;
}
