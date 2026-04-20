/*
 * Copyright (c) 2025, the Jeandle-JDK Authors. All Rights Reserved.
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

#include "jeandle/jeandleRuntimeRoutine.hpp"

#include "jeandle/__hotspotHeadersBegin__.hpp"
#include "asm/macroAssembler.hpp"
#include "asm/macroAssembler.inline.hpp"
#include "code/codeBlob.hpp"
#include "compiler/oopMap.hpp"
#include "memory/resourceArea.hpp"
#include "runtime/interfaceSupport.inline.hpp"
#include "runtime/stubRoutines.hpp"

#define __ masm->

// When a Jeandle compiled method throwing an exception, patch its return address to exceptional_return blob.
JRT_LEAF(void, JeandleRuntimeRoutine::install_exceptional_return(oopDesc* exception, JavaThread* current))
  assert(oopDesc::is_oop(exception), "must be a valid oop");
  RegisterMap r_map(current,
                    RegisterMap::UpdateMap::skip,
                    RegisterMap::ProcessFrames::include,
                    RegisterMap::WalkContinuation::skip);
  frame exception_frame = current->last_frame().sender(&r_map);
  CodeBlob* exception_code = exception_frame.cb();
  guarantee(exception_code != nullptr && exception_code->is_compiled_by_jeandle(), "install_exceptional_return must be jumped from jeandle compiled method");

  intptr_t* sender_sp = exception_frame.unextended_sp() + exception_code->frame_size();

  address* return_address = (address*)(sender_sp - 1);

  current->set_exception_pc(pauth_strip_verifiable(*return_address));
  current->set_exception_oop(exception);

  // Change the return address to exceptional return blob.
  *return_address = pauth_sign_return_address(_routine_entry[_exceptional_return]);
JRT_END

// When a Jeandle C routine throwing an exception, patch its return address to exceptional_return blob.
JRT_LEAF(void, JeandleRuntimeRoutine::install_exceptional_return_for_call_vm())
  JavaThread* current = JavaThread::current();
  assert(oopDesc::is_oop(current->pending_exception()), "must be a valid oop");
  frame routine_frame = current->last_frame();
  CodeBlob* routine_code = routine_frame.cb();
  guarantee(routine_code != nullptr, "routine_code must not be null");

  intptr_t* routine_sp = routine_frame.unextended_sp() + routine_code->frame_size();

  address* return_address = (address*)(routine_sp - 1);

  current->set_exception_pc(pauth_strip_verifiable(*return_address));
  current->set_exception_oop(current->pending_exception());
  current->clear_pending_exception();

  // Change the return address to exceptional return blob.
  *return_address = pauth_sign_return_address(_routine_entry[_exceptional_return]);
JRT_END

// When a Jeandle compiled method throwing an exception, its return address
// will be patched to this blob. Here we find the right exception handler,
// then jump to.
// The exception oop and the exception pc have been set by
// JeandleRuntimeRoutine::install_exceptional_return.
// On exit, we have exception oop in r0 and exception pc in r3.
void JeandleRuntimeRoutine::generate_exceptional_return() {
  // Allocate space for the code
  ResourceMark rm;
  // Setup code generation tools
  CodeBuffer buffer(_exceptional_return, 1024, 512);
  MacroAssembler* masm = new MacroAssembler(&buffer);

  const Register retval = r0;

  // Results:
  const Register exception_oop = r0;
  const Register exception_pc  = r3;

  address start = __ pc();

  // Get the exception pc
  __ ldr(exception_pc, Address(rthread, JavaThread::exception_pc_offset()));

  // Push the exception pc as return address. (for stack unwinding)
  __ stp(rfp, exception_pc, Address(__ pre(sp, -2 * wordSize)));

  address frame_complete = __ pc();

  {
    Label retaddr;
    __ set_last_Java_frame(sp, noreg, retaddr, rscratch1);
    __ mov(c_rarg0, rthread);
    __ lea(rscratch1, RuntimeAddress(CAST_FROM_FN_PTR(address, JeandleRuntimeRoutine::get_exception_handler)));
    __ blr(rscratch1);
    __ bind(retaddr);
  }

  OopMapSet* oop_maps = new OopMapSet();

  oop_maps->add_gc_map(__ pc() - start, new OopMap(4 /* frame_size in slot_size(4 bytes) */, 0));

  __ reset_last_Java_frame(false);

  // Now the exception handler is in retval.
  __ mov(rscratch1, retval);

  // Move the exception oop to r0. Exception handler will use this.
  __ ldr(exception_oop, Address(rthread, JavaThread::exception_oop_offset()));

  // Clear the exception oop so GC no longer processes it as a root.
  __ str(zr, Address(rthread, JavaThread::exception_oop_offset()));

  // For not confusing exception handler, clear the exception pc.
  __ str(zr, Address(rthread, JavaThread::exception_pc_offset()));
  
  // Pop the exception pc to r3. Exception handler will use this.
  __ ldp(rfp, exception_pc, Address(__ post(sp, 2 * wordSize)));

  // Jump to the exception handler.
  __ br(rscratch1);

  // Make sure all code is generated
  masm->flush();

  RuntimeStub* rs = RuntimeStub::new_runtime_stub(_exceptional_return,
                                                  &buffer,
                                                  frame_complete - start,
                                                  2 /* frame size */,
                                                  oop_maps,
                                                  false);

  _routine_entry[_exceptional_return] = rs->entry_point();
}

// C-callable adapter stub for StringCoding.countPositives on AArch64.
//
// Jeandle calls this stub via standard C ABI:
//   x0 = ba_start  (jbyte* — pointer to ba[off] in the Java heap)
//   w1 = len       (jint   — number of bytes to scan)
//
// MacroAssembler::count_positives(ary1=r1, len=r2, result=r0) expects:
//   r1 = ary1      (array pointer)
//   r2 = len       (length, 32-bit)
//   r0 = result    (initialised to len by the first instruction inside count_positives)
//
// The adapter:
//   1. enter() — saves fp and lr (lr will be clobbered by trampoline_call inside
//      count_positives when large/edge-case arrays fall through to the stub)
//   2. Rearrange registers: x2 ← ZeroExtend(w1) (len), r1 ← x0 (ba_start)
//      Note: w1 is a jint; AAPCS64 leaves the upper 32 bits of x1 unspecified.
//      count_positives operates on the full 64-bit x2, so we must zero-extend.
//   3. Emit MacroAssembler::count_positives(r1, r2, r0) inline — handles short arrays
//      directly; falls through to the DONE label after the counting loop or stub call.
//   4. leave() + ret(lr) — restore caller's frame and return (result in x0/r0).
void JeandleRuntimeRoutine::generate_count_positives_adapter() {
  // The AArch64 MacroAssembler::count_positives emits a trampoline call to
  // StubRoutines::aarch64::count_positives() at the STUB label.  That stub is
  // generated by stubGenerator_aarch64 during stubRoutines_init2(), which runs
  // BEFORE JeandleCompiler::initialize().  Guard defensively: if the stub is
  // somehow null (e.g. in a stripped or partial build), fall back to the scalar
  // wrapper rather than crashing inside count_positives().
  if (StubRoutines::aarch64::count_positives() == nullptr) {
    return; // scalar fallback (_count_positives_stub_adapter stays null)
  }

  ResourceMark rm;
  // 8 KB is ample: count_positives inline code is ~60 instructions plus trampolines.
  CodeBuffer cb("jeandle_count_positives_aarch64", 8192, 512);
  MacroAssembler masm(&cb);

  address start = masm.pc();
  // Save fp and lr: the trampoline_call inside count_positives (for STUB/STUB_LONG
  // paths) uses 'bl', which overwrites lr.  enter() pushes {fp, lr} so that the
  // original caller lr is safe across the inner stub calls.
  masm.enter();

  address frame_complete = masm.pc();

  // Rearrange: AAPCS64 entry is (x0=ba_start, w1=len).
  // count_positives expects r1=ba_start, r2=len (full 64-bit).
  // Under AAPCS64 the upper 32 bits of x1 are unspecified for a jint argument;
  // count_positives uses full-width operations on len (subs(len, len, wordSize) etc.),
  // so the upper bits must be cleared explicitly with zero-extension.
  // Must copy len to r2 BEFORE overwriting r1 with ba_start (x0→r1 = x0→x1 would alias).
  masm.add(r2, zr, r1, ext::uxtw);  // x2 = ZeroExtend(w1): add x2, xzr, w1, uxtw #0
  masm.mov(r1, r0);                  // r1 = ba_start  (x0)

  // Emit the counting code.  On return from this C++ call, the MacroAssembler has
  // generated the full inline sequence including STUB/STUB_LONG trampoline branches.
  // Control falls through to the DONE label at the end; result is in r0.
  address end = masm.count_positives(r1, r2, r0);
  if (end == nullptr) {
    // Trampoline pool allocation failed — leave _count_positives_stub_adapter null
    // so the fallback scalar wrapper is used instead.
    return;
  }

  // Restore frame and return to Jeandle caller; result already in x0/r0.
  masm.leave();
  masm.ret(lr);
  masm.flush();

  OopMapSet* oop_maps = new OopMapSet();
  RuntimeStub* rs = RuntimeStub::new_runtime_stub(
      "jeandle_count_positives_aarch64",
      &cb,
      frame_complete - start,
      2 /* frame_size: enter() pushes fp+lr = 2 * wordSize */,
      oop_maps,
      false /* caller_must_gc_arguments */);
  _count_positives_stub_adapter = rs->entry_point();
}

// Exception handler for Jeandle compiled method.
// At the entry of exception handler, we already have exception oop in r0 and exception pc in r3.
// What we need to do is to find the right landingpad according to the exception pc, then jump into it.
void JeandleRuntimeRoutine::generate_exception_handler() {
  // Allocate space for the code
  ResourceMark rm;
  // Setup code generation tools
  CodeBuffer buffer(_exception_handler, 1024, 512);
  MacroAssembler* masm = new MacroAssembler(&buffer);

  const Register retval = r0;

  // incoming parameters
  const Register exception_oop = r0;
  const Register exception_pc  = r3;

  address start = __ pc();

  // Push the exception pc as return address. (for stack unwinding)
  __ stp(rfp, exception_pc, Address(__ pre(sp, -2 * wordSize)));

  // Set exception oop and exception pc
  __ str(exception_oop, Address(rthread, JavaThread::exception_oop_offset()));
  __ str(exception_pc, Address(rthread, JavaThread::exception_pc_offset()));

  address frame_complete = __ pc();

  {
    Label retaddr;
    __ set_last_Java_frame(sp, noreg, retaddr, rscratch1);
    __ mov(c_rarg0, rthread);
    __ lea(rscratch1, RuntimeAddress(CAST_FROM_FN_PTR(address, JeandleRuntimeRoutine::search_landingpad)));
    __ blr(rscratch1);
    __ bind(retaddr);
  }

  OopMapSet* oop_maps = new OopMapSet();

  oop_maps->add_gc_map(__ pc() - start, new OopMap(4 /* frame_size in slot_size(4 bytes) */, 0));

  __ reset_last_Java_frame(false);

  // Clear the exception pc.
  __ str(zr, Address(rthread, JavaThread::exception_pc_offset()));

  __ ldp(rfp, exception_pc, Address(__ post(sp, 2 * wordSize)));

  // Jump to the landingpad.
  __ br(retval);

  // Make sure all code is generated
  masm->flush();

  RuntimeStub* rs = RuntimeStub::new_runtime_stub(_exception_handler,
                                                  &buffer,
                                                  frame_complete - start,
                                                  2 /* frame size */,
                                                  oop_maps,
                                                  false);

  _routine_entry[_exception_handler] = rs->entry_point();
}

void JeandleRuntimeRoutine::generate_deopt_blob() {
  _routine_entry[_deopt_blob] = SharedRuntime::deopt_blob()->unpack();
}
