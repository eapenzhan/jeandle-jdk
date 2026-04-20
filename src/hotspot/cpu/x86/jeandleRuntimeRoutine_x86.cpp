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
#include "opto/c2_MacroAssembler.hpp"
#include "code/codeBlob.hpp"
#include "compiler/oopMap.hpp"
#include "memory/resourceArea.hpp"
#include "oops/oopsHierarchy.hpp"
#include "runtime/frame.hpp"
#include "runtime/interfaceSupport.inline.hpp"

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

  current->set_exception_pc(*return_address);
  current->set_exception_oop(exception);

  // Change the return address to exceptional return blob.
  *return_address = _routine_entry[_exceptional_return];
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

  current->set_exception_pc(*return_address);
  current->set_exception_oop(current->pending_exception());
  current->clear_pending_exception();

  // Change the return address to exceptional return blob.
  *return_address = _routine_entry[_exceptional_return];
JRT_END

// C-callable adapter stub for StringCoding.countPositives on x86-64.
//
// Jeandle calls this stub via SysV AMD64 ABI:
//   rdi = ba_start  (jbyte* — pointer to ba[off] in the Java heap)
//   esi = len       (jint   — number of bytes to scan; esi = lower 32 bits of rsi)
//
// C2_MacroAssembler::count_positives(ary1=rsi, len=rcx, result=rax, tmp=rbx, xmm1, xmm2)
// generates all-inline SIMD code (SSE/AVX/AVX512 depending on CPU features);
// no calls out to other stubs.
//
// The adapter:
//   1. push rbx        — save callee-saved register used as a temp by count_positives
//   2. ecx ← esi       — save len to rcx BEFORE rsi is clobbered by the next move
//   3. rsi ← rdi       — rsi = ba_start (ary1)
//   4. count_positives(rsi, rcx, rax, rbx, xmm1, xmm2) — generates inline counting code
//   5. pop rbx; ret    — restore rbx and return (result in rax)
//
// xmm0-xmm7 are caller-saved in SysV AMD64 ABI; count_positives uses xmm1/xmm2 as
// TEMP (caller-saved), so no XMM save/restore is needed.
void JeandleRuntimeRoutine::generate_count_positives_adapter() {
#ifndef AMD64
  // 32-bit x86 builds: C2_MacroAssembler::count_positives uses 64-bit registers
  // and the SysV AMD64 ABI (rdi/rsi/rbx/xmm).  No 32-bit implementation is provided.
  // _count_positives_stub_adapter stays null; the scalar fallback is used instead.
  return;
#else
  ResourceMark rm;
  // 16 KB: count_positives inline code can be up to ~300 instructions for AVX512 path.
  CodeBuffer cb("jeandle_count_positives_x86", 16384, 512);
  C2_MacroAssembler masm(&cb);

  address start = masm.pc();

  // Prologue: save rbx (callee-saved in SysV ABI; KILL in count_positives).
  masm.push(rbx);

  // frame_complete marks the point after the prologue where the frame is fully
  // set up for stack walking.  push rbx decrements rsp by one 64-bit word, so
  // frame_complete is placed here (after the push) and frame_size = 1 below.
  address frame_complete = masm.pc();

  // Rearrange arguments.
  // esi = len at entry; save to ecx BEFORE clobbering rsi with the pointer.
  masm.movl(rcx, rsi);      // ecx = len
  masm.movptr(rsi, rdi);    // rsi = ba_start

  // Emit the inline SIMD counting code.
  // C2_MacroAssembler::count_positives initialises rax = len first (optimistic),
  // then subtracts as it finds negative bytes; result returned in rax.
  masm.count_positives(rsi, rcx, rax, rbx, xmm1, xmm2);

  // Epilogue.
  masm.pop(rbx);
  masm.ret(0);
  masm.flush();

  OopMapSet* oop_maps = new OopMapSet();
  RuntimeStub* rs = RuntimeStub::new_runtime_stub(
      "jeandle_count_positives_x86",
      &cb,
      frame_complete - start,
      1 /* frame_size: push rbx = one 64-bit slot (matches exceptional_return convention) */,
      oop_maps,
      false /* caller_must_gc_arguments */);
  _count_positives_stub_adapter = rs->entry_point();
#endif // AMD64
}

// When a Jeandle compiled method throwing an exception, its return address
// will be patched to this blob. Here we find the right exception handler,
// then jump to.
// The exception oop and the exception pc have been set by
// JeandleRuntimeRoutine::install_exceptional_return.
// On exit, we have exception oop in rax and exception pc in rdx.
void JeandleRuntimeRoutine::generate_exceptional_return() {
  // Allocate space for the code
  ResourceMark rm;
  // Setup code generation tools
  CodeBuffer buffer(_exceptional_return, 1024, 512);
  MacroAssembler* masm = new MacroAssembler(&buffer);

  address start = __ pc();

#ifdef ASSERT
  __ check_stack_alignment(rsp, "stack not aligned in Jeandle exceptional return");
#endif

  // Get the exception pc
  __ movptr(rax, Address(r15_thread, JavaThread::exception_pc_offset()));

  // Push the exception pc as return address. (for stack unwinding)
  __ push(rax);

  // rbp is an implicitly saved callee saved register (i.e., the calling
  // convention will save/restore it in the prolog/epilog).
  __ push(rbp);

  address frame_complete = __ pc();

  __ set_last_Java_frame(noreg, noreg, nullptr, rscratch1);

  __ mov(c_rarg0, r15_thread);
  __ call(RuntimeAddress(CAST_FROM_FN_PTR(address, JeandleRuntimeRoutine::get_exception_handler)));

  OopMapSet* oop_maps = new OopMapSet();

  oop_maps->add_gc_map(__ pc() - start, new OopMap(4 /* frame_size in slot_size(4 bytes) */, 0));

  __ reset_last_Java_frame(false);

  // Now the exception handler is in rax.
  __ mov(r10, rax);

  // Move the exception oop to rax. Exception handler will use this.
  __ movptr(rax, Address(r15_thread, JavaThread::exception_oop_offset()));

  // Clear the exception oop so GC no longer processes it as a root.
  __ movptr(Address(r15_thread, JavaThread::exception_oop_offset()), NULL_WORD);

  // For not confusing exception handler, clear the exception pc.
  __ movptr(Address(r15_thread, JavaThread::exception_pc_offset()), NULL_WORD);

  __ pop(rbp);

  // Pop the exception pc to rdx. Exception handler will use this.
  __ pop(rdx);

  // Jump to the exception handler.
  __ jmp(r10);

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

// Exception handler for Jeandle compiled method.
// At the entry of exception handler, we already have exception oop in rax and exception pc in rdx.
// What we need to do is to find the right landingpad according to the exception pc, then jump into it.
void JeandleRuntimeRoutine::generate_exception_handler() {
  // Allocate space for the code
  ResourceMark rm;
  // Setup code generation tools
  CodeBuffer buffer(_exception_handler, 1024, 512);
  MacroAssembler* masm = new MacroAssembler(&buffer);

  address start = __ pc();

#ifdef ASSERT
  __ check_stack_alignment(rsp, "stack not aligned in Jeandle exceptional handler");
#endif

  // Push the exception pc as return address. (for stack unwinding)
  __ push(rdx);

  // rbp is an implicitly saved callee saved register (i.e., the calling
  // convention will save/restore it in the prolog/epilog).
  __ push(rbp);

  // Set exception oop and exception pc
  __ movptr(Address(r15_thread, JavaThread::exception_oop_offset()),rax);
  __ movptr(Address(r15_thread, JavaThread::exception_pc_offset()), rdx);

  address frame_complete = __ pc();

  __ set_last_Java_frame(noreg, noreg, nullptr, rscratch1);

  __ mov(c_rarg0, r15_thread);
  __ call(RuntimeAddress(CAST_FROM_FN_PTR(address, JeandleRuntimeRoutine::search_landingpad)));

  OopMapSet* oop_maps = new OopMapSet();

  oop_maps->add_gc_map(__ pc() - start, new OopMap(4 /* frame_size in slot_size(4 bytes) */, 0));

  __ reset_last_Java_frame(false);

  // Clear the exception pc.
  __ movptr(Address(r15_thread, JavaThread::exception_pc_offset()), NULL_WORD);

  __ pop(rbp);

  __ pop(rdx);

  // Jump to the landingpad.
  __ jmp(rax);

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
