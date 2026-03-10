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
#include "memory/resourceArea.hpp"
#include "oops/oopsHierarchy.hpp"
#include "runtime/deoptimization.hpp"
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

// Copy directly from sharedRuntime_x86_64.cpp --------------------------------
class JeandleRegisterSaver {
  // Capture info about frame layout.  Layout offsets are in jint
  // units because compiler frame slots are jints.
#define XSAVE_AREA_BEGIN 160
#define XSAVE_AREA_YMM_BEGIN 576
#define XSAVE_AREA_OPMASK_BEGIN 1088
#define XSAVE_AREA_ZMM_BEGIN 1152
#define XSAVE_AREA_UPPERBANK 1664
#define DEF_XMM_OFFS(regnum)       xmm ## regnum ## _off = xmm_off + (regnum)*16/BytesPerInt, xmm ## regnum ## H_off
#define DEF_YMM_OFFS(regnum)       ymm ## regnum ## _off = ymm_off + (regnum)*16/BytesPerInt, ymm ## regnum ## H_off
#define DEF_ZMM_OFFS(regnum)       zmm ## regnum ## _off = zmm_off + (regnum)*32/BytesPerInt, zmm ## regnum ## H_off
#define DEF_OPMASK_OFFS(regnum)    opmask ## regnum ## _off = opmask_off + (regnum)*8/BytesPerInt,     opmask ## regnum ## H_off
#define DEF_ZMM_UPPER_OFFS(regnum) zmm ## regnum ## _off = zmm_upper_off + (regnum-16)*64/BytesPerInt, zmm ## regnum ## H_off
  enum layout {
    fpu_state_off = frame::arg_reg_save_area_bytes/BytesPerInt, // fxsave save area
    xmm_off       = fpu_state_off + XSAVE_AREA_BEGIN/BytesPerInt,            // offset in fxsave save area
    DEF_XMM_OFFS(0),
    DEF_XMM_OFFS(1),
    // 2..15 are implied in range usage
    ymm_off = xmm_off + (XSAVE_AREA_YMM_BEGIN - XSAVE_AREA_BEGIN)/BytesPerInt,
    DEF_YMM_OFFS(0),
    DEF_YMM_OFFS(1),
    // 2..15 are implied in range usage
    opmask_off         = xmm_off + (XSAVE_AREA_OPMASK_BEGIN - XSAVE_AREA_BEGIN)/BytesPerInt,
    DEF_OPMASK_OFFS(0),
    DEF_OPMASK_OFFS(1),
    // 2..7 are implied in range usage
    zmm_off = xmm_off + (XSAVE_AREA_ZMM_BEGIN - XSAVE_AREA_BEGIN)/BytesPerInt,
    DEF_ZMM_OFFS(0),
    DEF_ZMM_OFFS(1),
    zmm_upper_off = xmm_off + (XSAVE_AREA_UPPERBANK - XSAVE_AREA_BEGIN)/BytesPerInt,
    DEF_ZMM_UPPER_OFFS(16),
    DEF_ZMM_UPPER_OFFS(17),
    // 18..31 are implied in range usage
    fpu_state_end = fpu_state_off + ((FPUStateSizeInWords-1)*wordSize / BytesPerInt),
    fpu_stateH_end,
    r15_off, r15H_off,
    r14_off, r14H_off,
    r13_off, r13H_off,
    r12_off, r12H_off,
    r11_off, r11H_off,
    r10_off, r10H_off,
    r9_off,  r9H_off,
    r8_off,  r8H_off,
    rdi_off, rdiH_off,
    rsi_off, rsiH_off,
    ignore_off, ignoreH_off,  // extra copy of rbp
    rsp_off, rspH_off,
    rbx_off, rbxH_off,
    rdx_off, rdxH_off,
    rcx_off, rcxH_off,
    rax_off, raxH_off,
    // 16-byte stack alignment fill word: see MacroAssembler::push/pop_IU_state
    align_off, alignH_off,
    flags_off, flagsH_off,
    // The frame sender code expects that rbp will be in the "natural" place and
    // will override any oopMap setting for it. We must therefore force the layout
    // so that it agrees with the frame sender code.
    rbp_off, rbpH_off,        // copy of rbp we will restore
    return_off, returnH_off,  // slot for return address
    reg_save_size             // size in compiler stack slots
  };

 public:
  static OopMap* save_live_registers(MacroAssembler* masm, int additional_frame_words, int* total_frame_words, bool save_wide_vectors);
  static void restore_live_registers(MacroAssembler* masm, bool restore_wide_vectors = false);

  // Offsets into the register save area
  // Used by deoptimization when it is managing result register
  // values on its own

  static int rax_offset_in_bytes(void)    { return BytesPerInt * rax_off; }
  static int rdx_offset_in_bytes(void)    { return BytesPerInt * rdx_off; }
  static int rbx_offset_in_bytes(void)    { return BytesPerInt * rbx_off; }
  static int xmm0_offset_in_bytes(void)   { return BytesPerInt * xmm0_off; }
  static int return_offset_in_bytes(void) { return BytesPerInt * return_off; }

  // During deoptimization only the result registers need to be restored,
  // all the other values have already been extracted.
  static void restore_result_registers(MacroAssembler* masm);
};

OopMap* JeandleRegisterSaver::save_live_registers(MacroAssembler* masm, int additional_frame_words, int* total_frame_words, bool save_wide_vectors) {
  int off = 0;
  int num_xmm_regs = XMMRegister::available_xmm_registers();
#if COMPILER2_OR_JVMCI
  if (save_wide_vectors && UseAVX == 0) {
    save_wide_vectors = false; // vectors larger than 16 byte long are supported only with AVX
  }
  assert(!save_wide_vectors || MaxVectorSize <= 64, "Only up to 64 byte long vectors are supported");
#else
  save_wide_vectors = false; // vectors are generated only by C2 and JVMCI
#endif

  // Always make the frame size 16-byte aligned, both vector and non vector stacks are always allocated
  int frame_size_in_bytes = align_up(reg_save_size*BytesPerInt, num_xmm_regs);
  // OopMap frame size is in compiler stack slots (jint's) not bytes or words
  int frame_size_in_slots = frame_size_in_bytes / BytesPerInt;
  // CodeBlob frame size is in words.
  int frame_size_in_words = frame_size_in_bytes / wordSize;
  *total_frame_words = frame_size_in_words;

  // Save registers, fpu state, and flags.
  // We assume caller has already pushed the return address onto the
  // stack, so rsp is 8-byte aligned here.
  // We push rpb twice in this sequence because we want the real rbp
  // to be under the return like a normal enter.

  __ enter();          // rsp becomes 16-byte aligned here
  __ push_CPU_state(); // Push a multiple of 16 bytes

  // push cpu state handles this on EVEX enabled targets
  if (save_wide_vectors) {
    // Save upper half of YMM registers(0..15)
    int base_addr = XSAVE_AREA_YMM_BEGIN;
    for (int n = 0; n < 16; n++) {
      __ vextractf128_high(Address(rsp, base_addr+n*16), as_XMMRegister(n));
    }
    if (VM_Version::supports_evex()) {
      // Save upper half of ZMM registers(0..15)
      base_addr = XSAVE_AREA_ZMM_BEGIN;
      for (int n = 0; n < 16; n++) {
        __ vextractf64x4_high(Address(rsp, base_addr+n*32), as_XMMRegister(n));
      }
      // Save full ZMM registers(16..num_xmm_regs)
      base_addr = XSAVE_AREA_UPPERBANK;
      off = 0;
      int vector_len = Assembler::AVX_512bit;
      for (int n = 16; n < num_xmm_regs; n++) {
        __ evmovdqul(Address(rsp, base_addr+(off++*64)), as_XMMRegister(n), vector_len);
      }
#if COMPILER2_OR_JVMCI
      base_addr = XSAVE_AREA_OPMASK_BEGIN;
      off = 0;
      for(int n = 0; n < KRegister::number_of_registers; n++) {
        __ kmov(Address(rsp, base_addr+(off++*8)), as_KRegister(n));
      }
#endif
    }
  } else {
    if (VM_Version::supports_evex()) {
      // Save upper bank of XMM registers(16..31) for scalar or 16-byte vector usage
      int base_addr = XSAVE_AREA_UPPERBANK;
      off = 0;
      int vector_len = VM_Version::supports_avx512vl() ?  Assembler::AVX_128bit : Assembler::AVX_512bit;
      for (int n = 16; n < num_xmm_regs; n++) {
        __ evmovdqul(Address(rsp, base_addr+(off++*64)), as_XMMRegister(n), vector_len);
      }
#if COMPILER2_OR_JVMCI
      base_addr = XSAVE_AREA_OPMASK_BEGIN;
      off = 0;
      for(int n = 0; n < KRegister::number_of_registers; n++) {
        __ kmov(Address(rsp, base_addr+(off++*8)), as_KRegister(n));
      }
#endif
    }
  }
  __ vzeroupper();
  if (frame::arg_reg_save_area_bytes != 0) {
    // Allocate argument register save area
    __ subptr(rsp, frame::arg_reg_save_area_bytes);
  }

  // Set an oopmap for the call site.  This oopmap will map all
  // oop-registers and debug-info registers as callee-saved.  This
  // will allow deoptimization at this safepoint to find all possible
  // debug-info recordings, as well as let GC find all oops.

  OopMapSet *oop_maps = new OopMapSet();
  OopMap* map = new OopMap(frame_size_in_slots, 0);

#define STACK_OFFSET(x) VMRegImpl::stack2reg((x))

  map->set_callee_saved(STACK_OFFSET( rax_off ), rax->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( rcx_off ), rcx->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( rdx_off ), rdx->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( rbx_off ), rbx->as_VMReg());
  // rbp location is known implicitly by the frame sender code, needs no oopmap
  // and the location where rbp was saved by is ignored
  map->set_callee_saved(STACK_OFFSET( rsi_off ), rsi->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( rdi_off ), rdi->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( r8_off  ), r8->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( r9_off  ), r9->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( r10_off ), r10->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( r11_off ), r11->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( r12_off ), r12->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( r13_off ), r13->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( r14_off ), r14->as_VMReg());
  map->set_callee_saved(STACK_OFFSET( r15_off ), r15->as_VMReg());
  // For both AVX and EVEX we will use the legacy FXSAVE area for xmm0..xmm15,
  // on EVEX enabled targets, we get it included in the xsave area
  off = xmm0_off;
  int delta = xmm1_off - off;
  for (int n = 0; n < 16; n++) {
    XMMRegister xmm_name = as_XMMRegister(n);
    map->set_callee_saved(STACK_OFFSET(off), xmm_name->as_VMReg());
    off += delta;
  }
  if (UseAVX > 2) {
    // Obtain xmm16..xmm31 from the XSAVE area on EVEX enabled targets
    off = zmm16_off;
    delta = zmm17_off - off;
    for (int n = 16; n < num_xmm_regs; n++) {
      XMMRegister zmm_name = as_XMMRegister(n);
      map->set_callee_saved(STACK_OFFSET(off), zmm_name->as_VMReg());
      off += delta;
    }
  }

#if COMPILER2_OR_JVMCI
  if (save_wide_vectors) {
    // Save upper half of YMM registers(0..15)
    off = ymm0_off;
    delta = ymm1_off - ymm0_off;
    for (int n = 0; n < 16; n++) {
      XMMRegister ymm_name = as_XMMRegister(n);
      map->set_callee_saved(STACK_OFFSET(off), ymm_name->as_VMReg()->next(4));
      off += delta;
    }
    if (VM_Version::supports_evex()) {
      // Save upper half of ZMM registers(0..15)
      off = zmm0_off;
      delta = zmm1_off - zmm0_off;
      for (int n = 0; n < 16; n++) {
        XMMRegister zmm_name = as_XMMRegister(n);
        map->set_callee_saved(STACK_OFFSET(off), zmm_name->as_VMReg()->next(8));
        off += delta;
      }
    }
  }
#endif // COMPILER2_OR_JVMCI

  // %%% These should all be a waste but we'll keep things as they were for now
  if (true) {
    map->set_callee_saved(STACK_OFFSET( raxH_off ), rax->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( rcxH_off ), rcx->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( rdxH_off ), rdx->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( rbxH_off ), rbx->as_VMReg()->next());
    // rbp location is known implicitly by the frame sender code, needs no oopmap
    map->set_callee_saved(STACK_OFFSET( rsiH_off ), rsi->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( rdiH_off ), rdi->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( r8H_off  ), r8->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( r9H_off  ), r9->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( r10H_off ), r10->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( r11H_off ), r11->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( r12H_off ), r12->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( r13H_off ), r13->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( r14H_off ), r14->as_VMReg()->next());
    map->set_callee_saved(STACK_OFFSET( r15H_off ), r15->as_VMReg()->next());
    // For both AVX and EVEX we will use the legacy FXSAVE area for xmm0..xmm15,
    // on EVEX enabled targets, we get it included in the xsave area
    off = xmm0H_off;
    delta = xmm1H_off - off;
    for (int n = 0; n < 16; n++) {
      XMMRegister xmm_name = as_XMMRegister(n);
      map->set_callee_saved(STACK_OFFSET(off), xmm_name->as_VMReg()->next());
      off += delta;
    }
    if (UseAVX > 2) {
      // Obtain xmm16..xmm31 from the XSAVE area on EVEX enabled targets
      off = zmm16H_off;
      delta = zmm17H_off - off;
      for (int n = 16; n < num_xmm_regs; n++) {
        XMMRegister zmm_name = as_XMMRegister(n);
        map->set_callee_saved(STACK_OFFSET(off), zmm_name->as_VMReg()->next());
        off += delta;
      }
    }
  }

  return map;
}

void JeandleRegisterSaver::restore_live_registers(MacroAssembler* masm, bool restore_wide_vectors) {
  int num_xmm_regs = XMMRegister::available_xmm_registers();
  if (frame::arg_reg_save_area_bytes != 0) {
    // Pop arg register save area
    __ addptr(rsp, frame::arg_reg_save_area_bytes);
  }

#if COMPILER2_OR_JVMCI
  if (restore_wide_vectors) {
    assert(UseAVX > 0, "Vectors larger than 16 byte long are supported only with AVX");
    assert(MaxVectorSize <= 64, "Only up to 64 byte long vectors are supported");
  }
#else
  assert(!restore_wide_vectors, "vectors are generated only by C2");
#endif

  __ vzeroupper();

  // On EVEX enabled targets everything is handled in pop fpu state
  if (restore_wide_vectors) {
    // Restore upper half of YMM registers (0..15)
    int base_addr = XSAVE_AREA_YMM_BEGIN;
    for (int n = 0; n < 16; n++) {
      __ vinsertf128_high(as_XMMRegister(n), Address(rsp, base_addr+n*16));
    }
    if (VM_Version::supports_evex()) {
      // Restore upper half of ZMM registers (0..15)
      base_addr = XSAVE_AREA_ZMM_BEGIN;
      for (int n = 0; n < 16; n++) {
        __ vinsertf64x4_high(as_XMMRegister(n), Address(rsp, base_addr+n*32));
      }
      // Restore full ZMM registers(16..num_xmm_regs)
      base_addr = XSAVE_AREA_UPPERBANK;
      int vector_len = Assembler::AVX_512bit;
      int off = 0;
      for (int n = 16; n < num_xmm_regs; n++) {
        __ evmovdqul(as_XMMRegister(n), Address(rsp, base_addr+(off++*64)), vector_len);
      }
#if COMPILER2_OR_JVMCI
      base_addr = XSAVE_AREA_OPMASK_BEGIN;
      off = 0;
      for (int n = 0; n < KRegister::number_of_registers; n++) {
        __ kmov(as_KRegister(n), Address(rsp, base_addr+(off++*8)));
      }
#endif
    }
  } else {
    if (VM_Version::supports_evex()) {
      // Restore upper bank of XMM registers(16..31) for scalar or 16-byte vector usage
      int base_addr = XSAVE_AREA_UPPERBANK;
      int off = 0;
      int vector_len = VM_Version::supports_avx512vl() ?  Assembler::AVX_128bit : Assembler::AVX_512bit;
      for (int n = 16; n < num_xmm_regs; n++) {
        __ evmovdqul(as_XMMRegister(n), Address(rsp, base_addr+(off++*64)), vector_len);
      }
#if COMPILER2_OR_JVMCI
      base_addr = XSAVE_AREA_OPMASK_BEGIN;
      off = 0;
      for (int n = 0; n < KRegister::number_of_registers; n++) {
        __ kmov(as_KRegister(n), Address(rsp, base_addr+(off++*8)));
      }
#endif
    }
  }

  // Recover CPU state
  __ pop_CPU_state();
  // Get the rbp described implicitly by the calling convention (no oopMap)
  __ pop(rbp);
}

void JeandleRegisterSaver::restore_result_registers(MacroAssembler* masm) {

  // Just restore result register. Only used by deoptimization. By
  // now any callee save register that needs to be restored to a c2
  // caller of the deoptee has been extracted into the vframeArray
  // and will be stuffed into the c2i adapter we create for later
  // restoration so only result registers need to be restored here.

  // Restore fp result register
  __ movdbl(xmm0, Address(rsp, xmm0_offset_in_bytes()));
  // Restore integer result register
  __ movptr(rax, Address(rsp, rax_offset_in_bytes()));
  __ movptr(rdx, Address(rsp, rdx_offset_in_bytes()));

  // Pop all of the register save are off the stack except the return address
  __ addptr(rsp, return_offset_in_bytes());
}
// RegisterSaver End --------------------------------------------------------

//------------------------------generate_deopt_blob----------------------------
void JeandleRuntimeRoutine::generate_deopt_blob() {
  // Allocate space for the code
  ResourceMark rm;
  // Setup code generation tools
  int pad = 0;
  if (UseAVX > 2) {
    pad += 1024;
  }
  CodeBuffer buffer("deopt_blob", 2560+pad, 1024);
  MacroAssembler* masm = new MacroAssembler(&buffer);
  int frame_size_in_words;
  OopMap* map = nullptr;
  OopMapSet *oop_maps = new OopMapSet();

  // -------------
  // This code enters when returning to a de-optimized nmethod.  A return
  // address has been pushed on the stack, and return values are in
  // registers.
  // If we are doing a normal deopt then we were called from the patched
  // nmethod from the point we returned to the nmethod. So the return
  // address on the stack is wrong by NativeCall::instruction_size
  // We will adjust the value so it looks like we have the original return
  // address on the stack (like when we eagerly deoptimized).
  // In the case of an exception pending when deoptimizing, we enter
  // with a return address on the stack that points after the call we patched
  // into the exception handler. We have the following register state from,
  // e.g., the forward exception stub (see stubGenerator_x86_64.cpp).
  //    rax: exception oop
  //    rbx: exception handler
  //    rdx: throwing pc
  // So in this case we simply jam rdx into the useless return address and
  // the stack looks just like we want.
  //
  // At this point we need to de-opt.  We save the argument return
  // registers.  We call the first C routine, fetch_unroll_info().  This
  // routine captures the return values and returns a structure which
  // describes the current frame size and the sizes of all replacement frames.
  // The current frame is compiled code and may contain many inlined
  // functions, each with their own JVM state.  We pop the current frame, then
  // push all the new frames.  Then we call the C routine unpack_frames() to
  // populate these frames.  Finally unpack_frames() returns us the new target
  // address.  Notice that callee-save registers are BLOWN here; they have
  // already been captured in the vframeArray at the time the return PC was
  // patched.
  address start = __ pc();
  Label cont;

  // Prolog for non exception case!

  // Save everything in sight.
  map = JeandleRegisterSaver::save_live_registers(masm, 0, &frame_size_in_words, /*save_wide_vectors*/ true);

  // Normal deoptimization.  Save exec mode for unpack_frames.
  __ movl(r14, Deoptimization::Unpack_deopt); // callee-saved
  __ jmp(cont);

  int reexecute_offset = __ pc() - start;

  // Reexecute case
  // return address is the pc describes what bci to do re-execute at

  // No need to update map as each call to save_live_registers will produce identical oopmap
  (void) JeandleRegisterSaver::save_live_registers(masm, 0, &frame_size_in_words, /*save_wide_vectors*/ true);

  __ movl(r14, Deoptimization::Unpack_reexecute); // callee-saved
  __ jmp(cont);

  int exception_offset = __ pc() - start;

  // Prolog for exception case

  // all registers are dead at this entry point, except for rax, and
  // rdx which contain the exception oop and exception pc
  // respectively.  Set them in TLS and fall thru to the
  // unpack_with_exception_in_tls entry point.

  __ movptr(Address(r15_thread, JavaThread::exception_pc_offset()), rdx);
  __ movptr(Address(r15_thread, JavaThread::exception_oop_offset()), rax);

  int exception_in_tls_offset = __ pc() - start;

  // new implementation because exception oop is now passed in JavaThread

  // Prolog for exception case
  // All registers must be preserved because they might be used by LinearScan
  // Exceptiop oop and throwing PC are passed in JavaThread
  // tos: stack at point of call to method that threw the exception (i.e. only
  // args are on the stack, no return address)

  // make room on stack for the return address
  // It will be patched later with the throwing pc. The correct value is not
  // available now because loading it from memory would destroy registers.
  __ push(0);

  // Save everything in sight.
  map = JeandleRegisterSaver::save_live_registers(masm, 0, &frame_size_in_words, /*save_wide_vectors*/ true);

  // Now it is safe to overwrite any register

  // Deopt during an exception.  Save exec mode for unpack_frames.
  __ movl(r14, Deoptimization::Unpack_exception); // callee-saved

  // load throwing pc from JavaThread and patch it as the return address
  // of the current frame. Then clear the field in JavaThread

  __ movptr(rdx, Address(r15_thread, JavaThread::exception_pc_offset()));
  __ movptr(Address(rbp, wordSize), rdx);
  __ movptr(Address(r15_thread, JavaThread::exception_pc_offset()), NULL_WORD);

#ifdef ASSERT
  // verify that there is really an exception oop in JavaThread
  __ movptr(rax, Address(r15_thread, JavaThread::exception_oop_offset()));
  __ verify_oop(rax);

  // verify that there is no pending exception
  Label no_pending_exception;
  __ movptr(rax, Address(r15_thread, Thread::pending_exception_offset()));
  __ testptr(rax, rax);
  __ jcc(Assembler::zero, no_pending_exception);
  __ stop("must not have pending exception here");
  __ bind(no_pending_exception);
#endif

  __ bind(cont);

  // Call C code.  Need thread and this frame, but NOT official VM entry
  // crud.  We cannot block on this call, no GC can happen.
  //
  // UnrollBlock* fetch_unroll_info(JavaThread* thread)

  // fetch_unroll_info needs to call last_java_frame().

  __ set_last_Java_frame(noreg, noreg, nullptr, rscratch1);
#ifdef ASSERT
  { Label L;
    __ cmpptr(Address(r15_thread, JavaThread::last_Java_fp_offset()), NULL_WORD);
    __ jcc(Assembler::equal, L);
    __ stop("SharedRuntime::generate_deopt_blob: last_Java_fp not cleared");
    __ bind(L);
  }
#endif // ASSERT
  __ mov(c_rarg0, r15_thread);
  __ movl(c_rarg1, r14); // exec_mode
  __ call(RuntimeAddress(CAST_FROM_FN_PTR(address, Deoptimization::fetch_unroll_info)));

  // Need to have an oopmap that tells fetch_unroll_info where to
  // find any register it might need.
  oop_maps->add_gc_map(__ pc() - start, map);

  __ reset_last_Java_frame(false);

  // Load UnrollBlock* into rdi
  __ mov(rdi, rax);

  __ movl(r14, Address(rdi, Deoptimization::UnrollBlock::unpack_kind_offset()));
   Label noException;
  __ cmpl(r14, Deoptimization::Unpack_exception);   // Was exception pending?
  __ jcc(Assembler::notEqual, noException);
  __ movptr(rax, Address(r15_thread, JavaThread::exception_oop_offset()));
  // QQQ this is useless it was null above
  __ movptr(rdx, Address(r15_thread, JavaThread::exception_pc_offset()));
  __ movptr(Address(r15_thread, JavaThread::exception_oop_offset()), NULL_WORD);
  __ movptr(Address(r15_thread, JavaThread::exception_pc_offset()), NULL_WORD);

  __ verify_oop(rax);

  // Overwrite the result registers with the exception results.
  __ movptr(Address(rsp, JeandleRegisterSaver::rax_offset_in_bytes()), rax);
  // I think this is useless
  __ movptr(Address(rsp, JeandleRegisterSaver::rdx_offset_in_bytes()), rdx);

  __ bind(noException);

  // Only register save data is on the stack.
  // Now restore the result registers.  Everything else is either dead
  // or captured in the vframeArray.
  JeandleRegisterSaver::restore_result_registers(masm);

  // All of the register save area has been popped of the stack. Only the
  // return address remains.

  // Pop all the frames we must move/replace.
  //
  // Frame picture (youngest to oldest)
  // 1: self-frame (no frame link)
  // 2: deopting frame  (no frame link)
  // 3: caller of deopting frame (could be compiled/interpreted).
  //
  // Note: by leaving the return address of self-frame on the stack
  // and using the size of frame 2 to adjust the stack
  // when we are done the return to frame 3 will still be on the stack.

  // Pop deoptimized frame
  __ movl(rcx, Address(rdi, Deoptimization::UnrollBlock::size_of_deoptimized_frame_offset()));
  __ addptr(rsp, rcx);

  // rsp should be pointing at the return address to the caller (3)

  // Pick up the initial fp we should save
  // restore rbp before stack bang because if stack overflow is thrown it needs to be pushed (and preserved)
  __ movptr(rbp, Address(rdi, Deoptimization::UnrollBlock::initial_info_offset()));

#ifdef ASSERT
  // Compilers generate code that bang the stack by as much as the
  // interpreter would need. So this stack banging should never
  // trigger a fault. Verify that it does not on non product builds.
  __ movl(rbx, Address(rdi, Deoptimization::UnrollBlock::total_frame_sizes_offset()));
  __ bang_stack_size(rbx, rcx);
#endif

  // Load address of array of frame pcs into rcx
  __ movptr(rcx, Address(rdi, Deoptimization::UnrollBlock::frame_pcs_offset()));

  // Trash the old pc
  __ addptr(rsp, wordSize);

  // Load address of array of frame sizes into rsi
  __ movptr(rsi, Address(rdi, Deoptimization::UnrollBlock::frame_sizes_offset()));

  // Load counter into rdx
  __ movl(rdx, Address(rdi, Deoptimization::UnrollBlock::number_of_frames_offset()));

  // Now adjust the caller's stack to make up for the extra locals
  // but record the original sp so that we can save it in the skeletal interpreter
  // frame and the stack walking of interpreter_sender will get the unextended sp
  // value and not the "real" sp value.

  const Register sender_sp = r8;

  __ mov(sender_sp, rsp);
  __ movl(rbx, Address(rdi,
                       Deoptimization::UnrollBlock::
                       caller_adjustment_offset()));
  __ subptr(rsp, rbx);

  // Push interpreter frames in a loop
  Label loop;
  __ bind(loop);
  __ movptr(rbx, Address(rsi, 0));      // Load frame size
  __ subptr(rbx, 2*wordSize);           // We'll push pc and ebp by hand
  __ pushptr(Address(rcx, 0));          // Save return address
  __ enter();                           // Save old & set new ebp
  __ subptr(rsp, rbx);                  // Prolog
  // This value is corrected by layout_activation_impl
  __ movptr(Address(rbp, frame::interpreter_frame_last_sp_offset * wordSize), NULL_WORD);
  __ movptr(Address(rbp, frame::interpreter_frame_sender_sp_offset * wordSize), sender_sp); // Make it walkable
  __ mov(sender_sp, rsp);               // Pass sender_sp to next frame
  __ addptr(rsi, wordSize);             // Bump array pointer (sizes)
  __ addptr(rcx, wordSize);             // Bump array pointer (pcs)
  __ decrementl(rdx);                   // Decrement counter
  __ jcc(Assembler::notZero, loop);
  __ pushptr(Address(rcx, 0));          // Save final return address

  // Re-push self-frame
  __ enter();                           // Save old & set new ebp

  // Allocate a full sized register save area.
  // Return address and rbp are in place, so we allocate two less words.
  __ subptr(rsp, (frame_size_in_words - 2) * wordSize);

  // Restore frame locals after moving the frame
  __ movdbl(Address(rsp, JeandleRegisterSaver::xmm0_offset_in_bytes()), xmm0);
  __ movptr(Address(rsp, JeandleRegisterSaver::rax_offset_in_bytes()), rax);

  // Call C code.  Need thread but NOT official VM entry
  // crud.  We cannot block on this call, no GC can happen.  Call should
  // restore return values to their stack-slots with the new SP.
  //
  // void Deoptimization::unpack_frames(JavaThread* thread, int exec_mode)

  // Use rbp because the frames look interpreted now
  // Save "the_pc" since it cannot easily be retrieved using the last_java_SP after we aligned SP.
  // Don't need the precise return PC here, just precise enough to point into this code blob.
  address the_pc = __ pc();
  __ set_last_Java_frame(noreg, rbp, the_pc, rscratch1);

  __ andptr(rsp, -(StackAlignmentInBytes));  // Fix stack alignment as required by ABI
  __ mov(c_rarg0, r15_thread);
  __ movl(c_rarg1, r14); // second arg: exec_mode
  __ call(RuntimeAddress(CAST_FROM_FN_PTR(address, Deoptimization::unpack_frames)));
  // Revert SP alignment after call since we're going to do some SP relative addressing below
  __ movptr(rsp, Address(r15_thread, JavaThread::last_Java_sp_offset()));

  // Set an oopmap for the call site
  // Use the same PC we used for the last java frame
  oop_maps->add_gc_map(the_pc - start,
                       new OopMap( frame_size_in_words, 0 ));

  // Clear fp AND pc
  __ reset_last_Java_frame(true);

  // Collect return values
  __ movdbl(xmm0, Address(rsp, JeandleRegisterSaver::xmm0_offset_in_bytes()));
  __ movptr(rax, Address(rsp, JeandleRegisterSaver::rax_offset_in_bytes()));
  // I think this is useless (throwing pc?)
  __ movptr(rdx, Address(rsp, JeandleRegisterSaver::rdx_offset_in_bytes()));

  // Pop self-frame.
  __ leave();                           // Epilog

  // Jump to interpreter
  __ ret(0);

  // Make sure all code is generated
  masm->flush();

  _raw_deopt_blob = DeoptimizationBlob::create(&buffer, oop_maps, 0, exception_offset, reexecute_offset, frame_size_in_words);
  _routine_entry[_deopt_blob] = _raw_deopt_blob->unpack();
}

void JeandleRuntimeRoutine::generate_deopt_blob_with_reexcution() {
  _routine_entry[_deopt_blob_with_reexcution] = _raw_deopt_blob->unpack_with_reexecution();
}

void JeandleRuntimeRoutine::generate_deopt_blob_with_exception() {
  _routine_entry[_deopt_blob_with_exception] = _raw_deopt_blob->unpack_with_exception();
}
