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

JeandleIntrinsicCapabilities JeandleIntrinsicSupport::query(const JeandleIntrinsicDescriptor& desc) {
  JeandleIntrinsicCapabilities caps{};

  caps.has_llvm_builtin   = desc.supports_llvm_intrinsic;
  caps.hotspot_preferred  = JeandleUseHotspotIntrinsics;

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
    default:
      break;
  }

  return caps;
}
