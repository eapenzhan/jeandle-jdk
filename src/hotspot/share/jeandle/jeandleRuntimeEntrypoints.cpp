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

#include "jeandle/jeandleRuntimeEntrypoints.hpp"

#include "jeandle/jeandleRuntimeRoutine.hpp"

static llvm::CallingConv::ID runtime_cc() {
  return llvm::CallingConv::C;
}

bool JeandleRuntimeEntrypoints::resolve_math(vmIntrinsics::ID id,
                                             JeandleIntrinsicImplKind impl_kind,
                                             llvm::Module& module,
                                             JeandleRuntimeEntrypoint& out) {
  out.calling_conv = runtime_cc();
  out.is_gc_leaf = true;
  out.well_known_name = nullptr;
  switch (id) {
    case vmIntrinsics::_dsin:
      out.well_known_name = "math.dsin";
      out.callee = impl_kind == JeandleIntrinsicImplKind::HotSpotStub ?
        JeandleRuntimeRoutine::StubRoutines_dsin_callee(module) :
        JeandleRuntimeRoutine::SharedRuntime_dsin_callee(module);
      return true;
    case vmIntrinsics::_dcos:
      out.well_known_name = "math.dcos";
      out.callee = impl_kind == JeandleIntrinsicImplKind::HotSpotStub ?
        JeandleRuntimeRoutine::StubRoutines_dcos_callee(module) :
        JeandleRuntimeRoutine::SharedRuntime_dcos_callee(module);
      return true;
    case vmIntrinsics::_dtan:
      out.well_known_name = "math.dtan";
      out.callee = impl_kind == JeandleIntrinsicImplKind::HotSpotStub ?
        JeandleRuntimeRoutine::StubRoutines_dtan_callee(module) :
        JeandleRuntimeRoutine::SharedRuntime_dtan_callee(module);
      return true;
    case vmIntrinsics::_dlog:
      out.well_known_name = "math.dlog";
      out.callee = impl_kind == JeandleIntrinsicImplKind::HotSpotStub ?
        JeandleRuntimeRoutine::StubRoutines_dlog_callee(module) :
        JeandleRuntimeRoutine::SharedRuntime_dlog_callee(module);
      return true;
    case vmIntrinsics::_dlog10:
      out.well_known_name = "math.dlog10";
      out.callee = impl_kind == JeandleIntrinsicImplKind::HotSpotStub ?
        JeandleRuntimeRoutine::StubRoutines_dlog10_callee(module) :
        JeandleRuntimeRoutine::SharedRuntime_dlog10_callee(module);
      return true;
    case vmIntrinsics::_dexp:
      out.well_known_name = "math.dexp";
      out.callee = impl_kind == JeandleIntrinsicImplKind::HotSpotStub ?
        JeandleRuntimeRoutine::StubRoutines_dexp_callee(module) :
        JeandleRuntimeRoutine::SharedRuntime_dexp_callee(module);
      return true;
    case vmIntrinsics::_dpow:
      out.well_known_name = "math.dpow";
      out.callee = impl_kind == JeandleIntrinsicImplKind::HotSpotStub ?
        JeandleRuntimeRoutine::StubRoutines_dpow_callee(module) :
        JeandleRuntimeRoutine::SharedRuntime_dpow_callee(module);
      return true;
    default:
      return false;
  }
}

bool JeandleRuntimeEntrypoints::resolve_count_positives(llvm::Module& module,
                                                         JeandleRuntimeEntrypoint& out) {
  out.calling_conv    = runtime_cc();
  out.is_gc_leaf      = true;
  out.well_known_name = "count_positives";
  // Prefer the platform SIMD adapter when available; fall back to the scalar C++ wrapper.
  if (JeandleRuntimeRoutine::count_positives_stub_adapter() != nullptr) {
    out.callee = JeandleRuntimeRoutine::JeandleRuntime_count_positives_adapter_callee(module);
  } else {
    out.callee = JeandleRuntimeRoutine::JeandleRuntime_count_positives_callee(module);
  }
  return true;
}
