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
#include "runtime/deoptimization.hpp"
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

// Copy directly from sharedRuntime_aarch64.cpp ---------------------------------
class JeandleRegisterSaver {
  const bool _save_vectors;
 public:
  JeandleRegisterSaver(bool save_vectors) : _save_vectors(save_vectors) {}

  OopMap* save_live_registers(MacroAssembler* masm, int additional_frame_words, int* total_frame_words);
  void restore_live_registers(MacroAssembler* masm);

  // Offsets into the register save area
  // Used by deoptimization when it is managing result register
  // values on its own

  int reg_offset_in_bytes(Register r);
  int r0_offset_in_bytes()    { return reg_offset_in_bytes(r0); }
  int rscratch1_offset_in_bytes()    { return reg_offset_in_bytes(rscratch1); }
  int v0_offset_in_bytes();

  // Total stack size in bytes for saving sve predicate registers.
  int total_sve_predicate_in_bytes();

  // Capture info about frame layout
  // Note this is only correct when not saving full vectors.
  enum layout {
                fpu_state_off = 0,
                fpu_state_end = fpu_state_off + FPUStateSizeInWords - 1,
                // The frame sender code expects that rfp will be in
                // the "natural" place and will override any oopMap
                // setting for it. We must therefore force the layout
                // so that it agrees with the frame sender code.
                r0_off = fpu_state_off + FPUStateSizeInWords,
                rfp_off = r0_off + (Register::number_of_registers - 2) * Register::max_slots_per_register,
                return_off = rfp_off + Register::max_slots_per_register,      // slot for return address
                reg_save_size = return_off + Register::max_slots_per_register};

};

int JeandleRegisterSaver::reg_offset_in_bytes(Register r) {
  // The integer registers are located above the floating point
  // registers in the stack frame pushed by save_live_registers() so the
  // offset depends on whether we are saving full vectors, and whether
  // those vectors are NEON or SVE.

  int slots_per_vect = FloatRegister::save_slots_per_register;

  if (_save_vectors) {
    slots_per_vect = FloatRegister::slots_per_neon_register;
  }

  int r0_offset = v0_offset_in_bytes() + (slots_per_vect * FloatRegister::number_of_registers) * BytesPerInt;
  return r0_offset + r->encoding() * wordSize;
}

int JeandleRegisterSaver::v0_offset_in_bytes() {
  // The floating point registers are located above the predicate registers if
  // they are present in the stack frame pushed by save_live_registers(). So the
  // offset depends on the saved total predicate vectors in the stack frame.
  return (total_sve_predicate_in_bytes() / VMRegImpl::stack_slot_size) * BytesPerInt;
}

int JeandleRegisterSaver::total_sve_predicate_in_bytes() {
  return 0;
}

OopMap* JeandleRegisterSaver::save_live_registers(MacroAssembler* masm, int additional_frame_words, int* total_frame_words) {
  bool use_sve = false;
  int sve_vector_size_in_bytes = 0;
  int sve_vector_size_in_slots = 0;
  int sve_predicate_size_in_slots = 0;
  int total_predicate_in_bytes = total_sve_predicate_in_bytes();
  int total_predicate_in_slots = total_predicate_in_bytes / VMRegImpl::stack_slot_size;

  if (_save_vectors) {
    int extra_save_slots_per_register = 0;
    // Save upper half of vector registers
    if (use_sve) {
      extra_save_slots_per_register = sve_vector_size_in_slots - FloatRegister::save_slots_per_register;
    } else {
      extra_save_slots_per_register = FloatRegister::extra_save_slots_per_neon_register;
    }
    int extra_vector_bytes = extra_save_slots_per_register *
                             VMRegImpl::stack_slot_size *
                             FloatRegister::number_of_registers;
    additional_frame_words += ((extra_vector_bytes + total_predicate_in_bytes) / wordSize);
  }

  int frame_size_in_bytes = align_up(additional_frame_words * wordSize +
                                     reg_save_size * BytesPerInt, 16);
  // OopMap frame size is in compiler stack slots (jint's) not bytes or words
  int frame_size_in_slots = frame_size_in_bytes / BytesPerInt;
  // The caller will allocate additional_frame_words
  int additional_frame_slots = additional_frame_words * wordSize / BytesPerInt;
  // CodeBlob frame size is in words.
  int frame_size_in_words = frame_size_in_bytes / wordSize;
  *total_frame_words = frame_size_in_words;

  // Save Integer and Float registers.
  __ enter();
  __ push_CPU_state(_save_vectors, use_sve, sve_vector_size_in_bytes, total_predicate_in_bytes);

  // Set an oopmap for the call site.  This oopmap will map all
  // oop-registers and debug-info registers as callee-saved.  This
  // will allow deoptimization at this safepoint to find all possible
  // debug-info recordings, as well as let GC find all oops.

  OopMapSet *oop_maps = new OopMapSet();
  OopMap* oop_map = new OopMap(frame_size_in_slots, 0);

  for (int i = 0; i < Register::number_of_registers; i++) {
    Register r = as_Register(i);
    if (i <= rfp->encoding() && r != rscratch1 && r != rscratch2) {
      // SP offsets are in 4-byte words.
      // Register slots are 8 bytes wide, 32 floating-point registers.
      int sp_offset = Register::max_slots_per_register * i +
                      FloatRegister::save_slots_per_register * FloatRegister::number_of_registers;
      oop_map->set_callee_saved(VMRegImpl::stack2reg(sp_offset + additional_frame_slots), r->as_VMReg());
    }
  }

  for (int i = 0; i < FloatRegister::number_of_registers; i++) {
    FloatRegister r = as_FloatRegister(i);
    int sp_offset = 0;
    if (_save_vectors) {
      sp_offset = use_sve ? (total_predicate_in_slots + sve_vector_size_in_slots * i) :
                            (FloatRegister::slots_per_neon_register * i);
    } else {
      sp_offset = FloatRegister::save_slots_per_register * i;
    }
    oop_map->set_callee_saved(VMRegImpl::stack2reg(sp_offset), r->as_VMReg());
  }

  return oop_map;
}

void JeandleRegisterSaver::restore_live_registers(MacroAssembler* masm) {
  assert(!_save_vectors, "vectors are generated only by C2 and JVMCI");
  __ pop_CPU_state(_save_vectors);
  __ ldp(rfp, lr, Address(__ post(sp, 2 * wordSize)));
  __ authenticate_return_address();
} // RegisterSaver End

//------------------------------generate_deopt_blob----------------------------
void JeandleRuntimeRoutine::generate_deopt_blob() {
  // Allocate space for the code
  ResourceMark rm;
  // Setup code generation tools
  CodeBuffer buffer("deopt_blob", 2048, 1024);
  MacroAssembler* masm = new MacroAssembler(&buffer);
  int frame_size_in_words;
  OopMap* map = nullptr;
  OopMapSet *oop_maps = new OopMapSet();
  JeandleRegisterSaver reg_save(false);

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
  //    r0: exception oop
  //    r19: exception handler
  //    r3: throwing pc
  // So in this case we simply jam r3 into the useless return address and
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
  map = reg_save.save_live_registers(masm, 0, &frame_size_in_words);

  // Normal deoptimization.  Save exec mode for unpack_frames.
  __ movw(rcpool, Deoptimization::Unpack_deopt); // callee-saved
  __ b(cont);

  int reexecute_offset = __ pc() - start;

  // Reexecute case
  // return address is the pc describes what bci to do re-execute at

  // No need to update map as each call to save_live_registers will produce identical oopmap
  (void) reg_save.save_live_registers(masm, 0, &frame_size_in_words);

  __ movw(rcpool, Deoptimization::Unpack_reexecute); // callee-saved
  __ b(cont);

  int exception_offset = __ pc() - start;

  // Prolog for exception case

  // all registers are dead at this entry point, except for r0, and
  // r3 which contain the exception oop and exception pc
  // respectively.  Set them in TLS and fall thru to the
  // unpack_with_exception_in_tls entry point.

  __ str(r3, Address(rthread, JavaThread::exception_pc_offset()));
  __ str(r0, Address(rthread, JavaThread::exception_oop_offset()));

  int exception_in_tls_offset = __ pc() - start;

  // new implementation because exception oop is now passed in JavaThread

  // Prolog for exception case
  // All registers must be preserved because they might be used by LinearScan
  // Exceptiop oop and throwing PC are passed in JavaThread
  // tos: stack at point of call to method that threw the exception (i.e. only
  // args are on the stack, no return address)

  // The return address pushed by save_live_registers will be patched
  // later with the throwing pc. The correct value is not available
  // now because loading it from memory would destroy registers.

  // NB: The SP at this point must be the SP of the method that is
  // being deoptimized.  Deoptimization assumes that the frame created
  // here by save_live_registers is immediately below the method's SP.
  // This is a somewhat fragile mechanism.

  // Save everything in sight.
  map = reg_save.save_live_registers(masm, 0, &frame_size_in_words);

  // Now it is safe to overwrite any register

  // Deopt during an exception.  Save exec mode for unpack_frames.
  __ mov(rcpool, Deoptimization::Unpack_exception); // callee-saved

  // load throwing pc from JavaThread and patch it as the return address
  // of the current frame. Then clear the field in JavaThread
  __ ldr(r3, Address(rthread, JavaThread::exception_pc_offset()));
  __ protect_return_address(r3);
  __ str(r3, Address(rfp, wordSize));
  __ str(zr, Address(rthread, JavaThread::exception_pc_offset()));

#ifdef ASSERT
  // verify that there is really an exception oop in JavaThread
  __ ldr(r0, Address(rthread, JavaThread::exception_oop_offset()));
  __ verify_oop(r0);

  // verify that there is no pending exception
  Label no_pending_exception;
  __ ldr(rscratch1, Address(rthread, Thread::pending_exception_offset()));
  __ cbz(rscratch1, no_pending_exception);
  __ stop("must not have pending exception here");
  __ bind(no_pending_exception);
#endif

  __ bind(cont);

  // Call C code.  Need thread and this frame, but NOT official VM entry
  // crud.  We cannot block on this call, no GC can happen.
  //
  // UnrollBlock* fetch_unroll_info(JavaThread* thread)

  // fetch_unroll_info needs to call last_java_frame().

  Label retaddr;
  __ set_last_Java_frame(sp, noreg, retaddr, rscratch1);
#ifdef ASSERT
  { Label L;
    __ ldr(rscratch1, Address(rthread, JavaThread::last_Java_fp_offset()));
    __ cbz(rscratch1, L);
    __ stop("SharedRuntime::generate_deopt_blob: last_Java_fp not cleared");
    __ bind(L);
  }
#endif // ASSERT
  __ mov(c_rarg0, rthread);
  __ mov(c_rarg1, rcpool);
  __ lea(rscratch1, RuntimeAddress(CAST_FROM_FN_PTR(address, Deoptimization::fetch_unroll_info)));
  __ blr(rscratch1);
  __ bind(retaddr);

  // Need to have an oopmap that tells fetch_unroll_info where to
  // find any register it might need.
  oop_maps->add_gc_map(__ pc() - start, map);

  __ reset_last_Java_frame(false);

  // Load UnrollBlock* into r5
  __ mov(r5, r0);

  __ ldrw(rcpool, Address(r5, Deoptimization::UnrollBlock::unpack_kind_offset()));
   Label noException;
  __ cmpw(rcpool, Deoptimization::Unpack_exception);   // Was exception pending?
  __ br(Assembler::NE, noException);
  __ ldr(r0, Address(rthread, JavaThread::exception_oop_offset()));
  // QQQ this is useless it was null above
  __ ldr(r3, Address(rthread, JavaThread::exception_pc_offset()));
  __ str(zr, Address(rthread, JavaThread::exception_oop_offset()));
  __ str(zr, Address(rthread, JavaThread::exception_pc_offset()));

  __ verify_oop(r0);

  // Overwrite the result registers with the exception results.
  __ str(r0, Address(sp, reg_save.r0_offset_in_bytes()));
  // I think this is useless
  // __ str(r3, Address(sp, JeandleRegisterSaver::r3_offset_in_bytes()));

  __ bind(noException);

  // Only register save data is on the stack.
  // Now restore the result registers.  Everything else is either dead
  // or captured in the vframeArray.

  // Restore fp result register
  __ ldrd(v0, Address(sp, reg_save.v0_offset_in_bytes()));
  // Restore integer result register
  __ ldr(r0, Address(sp, reg_save.r0_offset_in_bytes()));

  // Pop all of the register save area off the stack
  __ add(sp, sp, frame_size_in_words * wordSize);

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
  __ ldrw(r2, Address(r5, Deoptimization::UnrollBlock::size_of_deoptimized_frame_offset()));
  __ sub(r2, r2, 2 * wordSize);
  __ add(sp, sp, r2);
  __ ldp(rfp, zr, __ post(sp, 2 * wordSize));

#ifdef ASSERT
  // Compilers generate code that bang the stack by as much as the
  // interpreter would need. So this stack banging should never
  // trigger a fault. Verify that it does not on non product builds.
  __ ldrw(r19, Address(r5, Deoptimization::UnrollBlock::total_frame_sizes_offset()));
  __ bang_stack_size(r19, r2);
#endif
  // Load address of array of frame pcs into r2
  __ ldr(r2, Address(r5, Deoptimization::UnrollBlock::frame_pcs_offset()));

  // Trash the old pc
  // __ addptr(sp, wordSize);  FIXME ????

  // Load address of array of frame sizes into r4
  __ ldr(r4, Address(r5, Deoptimization::UnrollBlock::frame_sizes_offset()));

  // Load counter into r3
  __ ldrw(r3, Address(r5, Deoptimization::UnrollBlock::number_of_frames_offset()));

  // Now adjust the caller's stack to make up for the extra locals
  // but record the original sp so that we can save it in the skeletal interpreter
  // frame and the stack walking of interpreter_sender will get the unextended sp
  // value and not the "real" sp value.

  const Register sender_sp = r6;

  __ mov(sender_sp, sp);
  __ ldrw(r19, Address(r5,
                       Deoptimization::UnrollBlock::
                       caller_adjustment_offset()));
  __ sub(sp, sp, r19);

  // Push interpreter frames in a loop
  __ mov(rscratch1, (uint64_t)0xDEADDEAD);        // Make a recognizable pattern
  __ mov(rscratch2, rscratch1);
  Label loop;
  __ bind(loop);
  __ ldr(r19, Address(__ post(r4, wordSize)));          // Load frame size
  __ sub(r19, r19, 2*wordSize);           // We'll push pc and fp by hand
  __ ldr(lr, Address(__ post(r2, wordSize)));  // Load pc
  __ enter();                           // Save old & set new fp
  __ sub(sp, sp, r19);                  // Prolog
  // This value is corrected by layout_activation_impl
  __ str(zr, Address(rfp, frame::interpreter_frame_last_sp_offset * wordSize));
  __ str(sender_sp, Address(rfp, frame::interpreter_frame_sender_sp_offset * wordSize)); // Make it walkable
  __ mov(sender_sp, sp);               // Pass sender_sp to next frame
  __ sub(r3, r3, 1);                   // Decrement counter
  __ cbnz(r3, loop);

    // Re-push self-frame
  __ ldr(lr, Address(r2));
  __ enter();

  // Allocate a full sized register save area.  We subtract 2 because
  // enter() just pushed 2 words
  __ sub(sp, sp, (frame_size_in_words - 2) * wordSize);

  // Restore frame locals after moving the frame
  __ strd(v0, Address(sp, reg_save.v0_offset_in_bytes()));
  __ str(r0, Address(sp, reg_save.r0_offset_in_bytes()));

  // Call C code.  Need thread but NOT official VM entry
  // crud.  We cannot block on this call, no GC can happen.  Call should
  // restore return values to their stack-slots with the new SP.
  //
  // void Deoptimization::unpack_frames(JavaThread* thread, int exec_mode)

  // Use rfp because the frames look interpreted now
  // Don't need the precise return PC here, just precise enough to point into this code blob.
  address the_pc = __ pc();
  __ set_last_Java_frame(sp, rfp, the_pc, rscratch1);

  __ mov(c_rarg0, rthread);
  __ movw(c_rarg1, rcpool); // second arg: exec_mode
  __ lea(rscratch1, RuntimeAddress(CAST_FROM_FN_PTR(address, Deoptimization::unpack_frames)));
  __ blr(rscratch1);

  // Set an oopmap for the call site
  // Use the same PC we used for the last java frame
  oop_maps->add_gc_map(the_pc - start,
                       new OopMap( frame_size_in_words, 0 ));

  // Clear fp AND pc
  __ reset_last_Java_frame(true);

  // Collect return values
  __ ldrd(v0, Address(sp, reg_save.v0_offset_in_bytes()));
  __ ldr(r0, Address(sp, reg_save.r0_offset_in_bytes()));
  // I think this is useless (throwing pc?)
  // __ ldr(r3, Address(sp, JeandleRegisterSaver::r3_offset_in_bytes()));

  // Pop self-frame.
  __ leave();                           // Epilog

  // Jump to interpreter
  __ ret(lr);

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
