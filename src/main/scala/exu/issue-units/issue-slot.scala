//******************************************************************************
// Copyright (c) 2015 - 2018, The Regents of the University of California (Regents).
// All Rights Reserved. See LICENSE and LICENSE.SiFive for license details.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
// RISCV Processor Issue Slot Logic
//--------------------------------------------------------------------------
//------------------------------------------------------------------------------
//
// Note: stores (and AMOs) are "broken down" into 2 uops, but stored within a single issue-slot.
// TODO XXX make a separate issueSlot for MemoryIssueSlots, and only they break apart stores.
// TODO Disable ldspec for FP queue.

package boom.exu

import chisel3._
import chisel3.util._

import freechips.rocketchip.config.Parameters

import boom.common._
import boom.util._
import FUConstants._

/**
 * IO bundle to interact with Issue slot
 *
 * @param numWakeupPorts number of wakeup ports for the slot
 */
class IssueSlotIO(val numWakeupPorts: Int)(implicit p: Parameters) extends BoomBundle
{
  val valid         = Output(Bool())
  val will_be_valid = Output(Bool()) // TODO code review, do we need this signal so explicitely?
  val request       = Output(Bool())
  val request_hp    = Output(Bool())
  val grant         = Input(Bool())

  val brupdate        = Input(new BrUpdateInfo())
  val kill          = Input(Bool()) // pipeline flush
  val clear         = Input(Bool()) // entry being moved elsewhere (not mutually exclusive with grant)
  val ldspec_miss   = Input(Bool()) // Previous cycle's speculative load wakeup was mispredicted.

  val wakeup_ports  = Flipped(Vec(numWakeupPorts, Valid(new IqWakeup(maxPregSz))))
  val pred_wakeup_port = Flipped(Valid(UInt(log2Ceil(ftqSz).W)))
  val spec_ld_wakeup = Flipped(Vec(memWidth, Valid(UInt(width=maxPregSz.W))))
  val in_uop        = Flipped(Valid(new MicroOp())) // if valid, this WILL overwrite an entry!
  val out_uop   = Output(new MicroOp()) // the updated slot uop; will be shifted upwards in a collasping queue.
  val uop           = Output(new MicroOp()) // the current Slot's uop. Sent down the pipeline when issued.
  
  //specshieldERP+ 
  val shadow_regfile   = Input(Vec(numIntPhysRegs, UInt(1.W)))

  // fast-bypass
  val fast_bypass = Flipped(Valid(new MicroOp()))  

  val debug = {
    val result = new Bundle {
      val p1 = Bool()
      val p2 = Bool()
      val p3 = Bool()
      val ppred = Bool()
      val state = UInt(width=2.W)
    }
    Output(result)
  }
}

/**
 * Single issue slot. Holds a uop within the issue queue
 *
 * @param numWakeupPorts number of wakeup ports
 */
class IssueSlot(val numWakeupPorts: Int)(implicit p: Parameters)
  extends BoomModule
  with IssueUnitConstants
{
  val io = IO(new IssueSlotIO(numWakeupPorts))

  // slot invalid?
  // slot is valid, holding 1 uop
  // slot is valid, holds 2 uops (like a store)
  def is_invalid = state === s_invalid
  def is_valid = state =/= s_invalid

  val next_state      = Wire(UInt()) // the next state of this slot (which might then get moved to a new slot)
  val next_uopc       = Wire(UInt()) // the next uopc of this slot (which might then get moved to a new slot)
  val next_lrs1_rtype = Wire(UInt()) // the next reg type of this slot (which might then get moved to a new slot)
  val next_lrs2_rtype = Wire(UInt()) // the next reg type of this slot (which might then get moved to a new slot)

  val state = RegInit(s_invalid)
  val p1    = RegInit(false.B)
  val p2    = RegInit(false.B)
  val p3    = RegInit(false.B)
  val ppred = RegInit(false.B)

  // Poison if woken up by speculative load.
  // Poison lasts 1 cycle (as ldMiss will come on the next cycle).
  // SO if poisoned is true, set it to false!
  val p1_poisoned = RegInit(false.B)
  val p2_poisoned = RegInit(false.B)
  p1_poisoned := false.B
  p2_poisoned := false.B
  val next_p1_poisoned = Mux(io.in_uop.valid, io.in_uop.bits.iw_p1_poisoned, p1_poisoned)
  val next_p2_poisoned = Mux(io.in_uop.valid, io.in_uop.bits.iw_p2_poisoned, p2_poisoned)

  val slot_uop = RegInit(NullMicroOp)
  val next_uop = Mux(io.in_uop.valid, io.in_uop.bits, slot_uop)

  //-----------------------------------------------------------------------------
  // next slot state computation
  // compute the next state for THIS entry slot (in a collasping queue, the
  // current uop may get moved elsewhere, and a new uop can enter

  when (io.kill) {
    state := s_invalid
  } .elsewhen (io.in_uop.valid) {
    state := io.in_uop.bits.iw_state
  } .elsewhen (io.clear) {
    state := s_invalid
  } .otherwise {
    state := next_state
  }

  //-----------------------------------------------------------------------------
  // "update" state
  // compute the next state for the micro-op in this slot. This micro-op may
  // be moved elsewhere, so the "next_state" travels with it.

  // defaults
  next_state := state
  next_uopc := slot_uop.uopc
  next_lrs1_rtype := slot_uop.lrs1_rtype
  next_lrs2_rtype := slot_uop.lrs2_rtype

  when (io.kill) {
    next_state := s_invalid
  } .elsewhen ((io.grant && (state === s_valid_1)) ||
    (io.grant && (state === s_valid_2) && p1 && p2 && ppred)) {
    // try to issue this uop.
    when (!(io.ldspec_miss && (p1_poisoned || p2_poisoned))) {
      next_state := s_invalid
    }
  } .elsewhen (io.grant && (state === s_valid_2)) {
    when (!(io.ldspec_miss && (p1_poisoned || p2_poisoned))) {
      next_state := s_valid_1
      when (p1) {
        slot_uop.uopc := uopSTD
        next_uopc := uopSTD
        slot_uop.lrs1_rtype := RT_X
        next_lrs1_rtype := RT_X
      } .otherwise {
        slot_uop.lrs2_rtype := RT_X
        next_lrs2_rtype := RT_X
      }
    }
  }

  when (io.in_uop.valid) {
    slot_uop := io.in_uop.bits
    assert (is_invalid || io.clear || io.kill, "trying to overwrite a valid issue slot.")
  }

  // Wakeup Compare Logic

  // these signals are the "next_p*" for the current slot's micro-op.
  // they are important for shifting the current slot_uop up to an other entry.
  val next_p1 = WireInit(p1)
  val next_p2 = WireInit(p2)
  val next_p3 = WireInit(p3)
  val next_ppred = WireInit(ppred)
 
//************************************************************
  // specshieldERP+ (this is the main source code which is commented)
  /*
  when (io.in_uop.valid) {
    p1 := !(io.in_uop.bits.prs1_busy)
    p2 := !(io.in_uop.bits.prs2_busy)
    p3 := !(io.in_uop.bits.prs3_busy)
    ppred := !(io.in_uop.bits.ppred_busy)
  }
  */
  
  //specshieldERP+ (temp value to store the wakeup effect)
  val tainted_wake_1_reg    = RegInit(false.B)
  val tainted_wake_2_reg    = RegInit(false.B)
  val tainted_wake_3_reg    = RegInit(false.B)
  val tainted_wake_1    = WireInit(tainted_wake_1_reg)
  val tainted_wake_2    = WireInit(tainted_wake_2_reg)
  val tainted_wake_3    = WireInit(tainted_wake_3_reg)
  val taint             = WireInit(false.B)
  //val tainted_wake_next    = RegNext(tainted_wake)

  //specshieldERP+ 
  // check whether the instruction is a load
  when (io.in_uop.valid && !io.in_uop.bits.uses_ldq) {
    p1 := !(io.in_uop.bits.prs1_busy)
    p2 := !(io.in_uop.bits.prs2_busy)
    p3 := !(io.in_uop.bits.prs3_busy)
    ppred := !(io.in_uop.bits.ppred_busy)
    tainted_wake_1 := false.B
    tainted_wake_2 := false.B
    tainted_wake_3 := false.B
  }
  //specshieldERP+ if it is a load check whether the source is tainted or not (through shadow reg)
  .elsewhen (io.in_uop.valid && io.in_uop.bits.uses_ldq) {

    p1 := !(io.in_uop.bits.prs1_busy) && !(io.shadow_regfile(io.in_uop.bits.prs1).asBool) && !(io.in_uop.bits.wake_tainted)
    //tainted_wake_1 := !(io.in_uop.bits.prs1_busy) && io.shadow_regfile(io.in_uop.bits.prs1).asBool
    slot_uop.prs1_tainted := !(io.in_uop.bits.prs1_busy) && (io.shadow_regfile(io.in_uop.bits.prs1).asBool || (io.in_uop.bits.wake_tainted))
    printf("NOTWAKEUP: setting up tainted wake for  %x prs1: %d prs1_busy: %d shadow_regfile: %d read_tainted_wake_1: %d\n", 
          io.in_uop.bits.debug_pc, io.in_uop.bits.prs1.asUInt, io.in_uop.bits.prs1_busy.asUInt, 
          io.shadow_regfile(io.in_uop.bits.prs1).asUInt,  
          (!(io.in_uop.bits.prs1_busy) && io.shadow_regfile(io.in_uop.bits.prs1).asBool).asUInt);
    
    p2 := !(io.in_uop.bits.prs2_busy) && !(io.shadow_regfile(io.in_uop.bits.prs2).asBool)
    //tainted_wake_2 := !(io.in_uop.bits.prs2_busy) && io.shadow_regfile(io.in_uop.bits.prs2).asBool
    slot_uop.prs2_tainted := !(io.in_uop.bits.prs2_busy) && (io.shadow_regfile(io.in_uop.bits.prs2).asBool || (io.in_uop.bits.wake_tainted))
    printf("NOTWAKEUP: setting up tainted wake for  %x tainted_wake_2: %d \n", 
          io.in_uop.bits.debug_pc, tainted_wake_2.asUInt);

    p3 := !(io.in_uop.bits.prs3_busy) && !(io.shadow_regfile(io.in_uop.bits.prs3).asBool)
    //tainted_wake_3 := !(io.in_uop.bits.prs3_busy) && io.shadow_regfile(io.in_uop.bits.prs3).asBool
    slot_uop.prs3_tainted := !(io.in_uop.bits.prs3_busy) && (io.shadow_regfile(io.in_uop.bits.prs3).asBool || (io.in_uop.bits.wake_tainted))
    printf("NOTWAKEUP: setting up tainted wake for  %x tainted_wake_3: %d \n", 
          io.in_uop.bits.debug_pc, tainted_wake_3.asUInt);

    ppred := !(io.in_uop.bits.ppred_busy)
  }
  //specshieldERP+ (added to check whether we can solve pk problem)
  .elsewhen (slot_uop.uses_ldq) {
    printf("pc: 0x%x is prs1 busy? %d is shadow regfile tainted? %d va natije: %d\n",slot_uop.debug_pc, slot_uop.prs1_busy.asUInt, io.shadow_regfile(slot_uop.prs1.asUInt), (!(slot_uop.prs1_busy) && !(io.shadow_regfile(slot_uop.prs1).asBool)).asUInt);
    //p1 := Mux(slot_uop.issue_ready, true.B, !(slot_uop.prs1_busy) && !(io.shadow_regfile(slot_uop.prs1).asBool))
    //p2 := !(slot_uop.prs2_busy) && !(io.shadow_regfile(slot_uop.prs2).asBool)
    //p3 := !(slot_uop.prs3_busy) && !(io.shadow_regfile(slot_uop.prs3).asBool)
    //Force prs3 to be true when p1 is true for loads(just experimenting!)
    p1 := !(slot_uop.prs1_busy) && !(io.shadow_regfile(slot_uop.prs1).asBool)
    p2 := true.B
    p3 := true.B
  }
  
  
//************************************************************

  // default code (specshield)
  /*
  when (io.in_uop.valid) {
    p1 := !(io.in_uop.bits.prs1_busy)
    p2 := !(io.in_uop.bits.prs2_busy)
    p3 := !(io.in_uop.bits.prs3_busy)
  }  
  */

  //fast-bypass 
  val temp_fast_bypass = Reg(new MicroOp())
  val received_fast_bypass = RegInit(false.B)
  when (io.fast_bypass.valid) {
    temp_fast_bypass := io.fast_bypass.bits
    received_fast_bypass := true.B
  }
  when (io.in_uop.valid  && received_fast_bypass.asBool && (temp_fast_bypass.pdst === io.in_uop.bits.prs1)) {
    printf("Halle DADA\n");
    p1 := true.B
    p2 := true.B
    p3 := true.B
    received_fast_bypass  := false.B
  }
  
  

  when (io.ldspec_miss && next_p1_poisoned) {
    assert(next_uop.prs1 =/= 0.U, "Poison bit can't be set for prs1=x0!")
    p1 := false.B
  }
  when (io.ldspec_miss && next_p2_poisoned) {
    assert(next_uop.prs2 =/= 0.U, "Poison bit can't be set for prs2=x0!")
    p2 := false.B
  }


  //specshieldERP+ (this part is the default source code which is commented out for ERP+)
  /*
  for (i <- 0 until numWakeupPorts) {
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs1)) {
      p1 := true.B
      //specshieldSTL
      printf("wakeup port match  prs1: %d\n", io.wakeup_ports(i).bits.pdst);
    }
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs2)) {
      p2 := true.B
     //specshieldSTL
      printf("wakeup port match  prs2: %d\n", io.wakeup_ports(i).bits.pdst);
    }
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs3)) {
      p3 := true.B
      //specshieldSTL
      printf("wakeup port match  prs3: %d\n", io.wakeup_ports(i).bits.pdst);
    }
  }
  */

  

  //specshieldERP+ 
  for (i <- 0 until numWakeupPorts) {
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs1) && 
         (!next_uop.uses_ldq || !io.shadow_regfile(io.wakeup_ports(i).bits.pdst).asBool) && 
         (!next_uop.uses_ldq || !io.wakeup_ports(i).bits.tainted)) {
      p1 := true.B
      tainted_wake_1 := false.B
      slot_uop.prs1_tainted := false.B
      //slot_uop.issue_ready:= true.B
      //specshieldSTL
      printf("wakeup port match  prs1: %d\n", io.wakeup_ports(i).bits.pdst);
    }
    .elsewhen(io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs1) && 
         (next_uop.uses_ldq && (io.shadow_regfile(io.wakeup_ports(i).bits.pdst).asBool || io.wakeup_ports(i).bits.tainted))){
          tainted_wake_1 := true.B
          slot_uop.prs1_tainted := true.B
          taint := io.wakeup_ports(i).bits.tainted
          printf("setting up tainted wake for  %x tainted_wake: %d \n", 
          next_uop.debug_pc, tainted_wake_1.asUInt);
    }
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs2) &&
         (!next_uop.uses_ldq || !io.shadow_regfile(io.wakeup_ports(i).bits.pdst).asBool) && 
         (!next_uop.uses_ldq || !io.wakeup_ports(i).bits.tainted)) {
      p2 := true.B
      tainted_wake_2 := false.B
      slot_uop.prs2_tainted := false.B
     //specshieldSTL
      printf("wakeup port match  prs2: %d\n", io.wakeup_ports(i).bits.pdst);
    }
    .elsewhen(io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs2) && 
         (next_uop.uses_ldq && (io.shadow_regfile(io.wakeup_ports(i).bits.pdst).asBool || io.wakeup_ports(i).bits.tainted))){
          tainted_wake_2 := true.B
          slot_uop.prs2_tainted := true.B
          printf("setting up tainted wake for  %x tainted_wake: %d \n", 
          next_uop.debug_pc, tainted_wake_2.asUInt);
    }
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs3) &&
         (!next_uop.uses_ldq || !io.shadow_regfile(io.wakeup_ports(i).bits.pdst).asBool) && 
         (!next_uop.uses_ldq || !io.wakeup_ports(i).bits.tainted)) {
      p3 := true.B
      tainted_wake_3 := false.B
      slot_uop.prs3_tainted := false.B
      //specshieldSTL
      printf("wakeup port match  prs3: %d\n", io.wakeup_ports(i).bits.pdst);
    }
    .elsewhen(io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs3) && 
         (next_uop.uses_ldq && (io.shadow_regfile(io.wakeup_ports(i).bits.pdst).asBool || io.wakeup_ports(i).bits.tainted))){
          tainted_wake_3 := true.B
          slot_uop.prs3_tainted := true.B
          printf("setting up tainted wake for  %x tainted_wake: %d \n", 
          next_uop.debug_pc, tainted_wake_3.asUInt);
    }
  }


  // default-code (specshield)
  /*
  for (i <- 0 until numWakeupPorts) {
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs1)) {
      p1 := true.B
    }
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs2)) {
      p2 := true.B
    }
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs3)) {
      p3 := true.B
    }
  }
  */







  when (io.pred_wakeup_port.valid && io.pred_wakeup_port.bits === next_uop.ppred) {
    ppred := true.B
  }

  for (w <- 0 until memWidth) {
    assert (!(io.spec_ld_wakeup(w).valid && io.spec_ld_wakeup(w).bits === 0.U),
      "Loads to x0 should never speculatively wakeup other instructions")
  }

  // TODO disable if FP IQ.
  
  for (w <- 0 until memWidth) {
    when (io.spec_ld_wakeup(w).valid &&
      io.spec_ld_wakeup(w).bits === next_uop.prs1 &&
      next_uop.lrs1_rtype === RT_FIX) {
      p1 := true.B
      p1_poisoned := true.B
      assert (!next_p1_poisoned)
    }
    when (io.spec_ld_wakeup(w).valid &&
      io.spec_ld_wakeup(w).bits === next_uop.prs2 &&
      next_uop.lrs2_rtype === RT_FIX) {
      p2 := true.B
      p2_poisoned := true.B
      assert (!next_p2_poisoned)
    }
  }


  // Handle branch misspeculations
  val next_br_mask = GetNewBrMask(io.brupdate, slot_uop)

  // was this micro-op killed by a branch? if yes, we can't let it be valid if
  // we compact it into an other entry
  when (IsKilledByBranch(io.brupdate, slot_uop)) {
    next_state := s_invalid
  }

  when (!io.in_uop.valid) {
    slot_uop.br_mask := next_br_mask
  }

  //-------------------------------------------------------------
  // Request Logic
  io.request := is_valid && p1 && p2 && p3 && ppred && !io.kill
  val high_priority = slot_uop.is_br || slot_uop.is_jal || slot_uop.is_jalr
  io.request_hp := io.request && high_priority

  when (state === s_valid_1) {
    io.request := p1 && p2 && p3 && ppred && !io.kill
  } .elsewhen (state === s_valid_2) {
    io.request := (p1 || p2) && ppred && !io.kill
  } .otherwise {
    io.request := false.B
  }

  //assign outputs
  io.valid := is_valid
  io.uop := slot_uop
  io.uop.iw_p1_poisoned := p1_poisoned
  io.uop.iw_p2_poisoned := p2_poisoned

  // micro-op will vacate due to grant.
  val may_vacate = io.grant && ((state === s_valid_1) || (state === s_valid_2) && p1 && p2 && ppred)
  val squash_grant = io.ldspec_miss && (p1_poisoned || p2_poisoned)
  io.will_be_valid := is_valid && !(may_vacate && !squash_grant)

  io.out_uop            := slot_uop
  io.out_uop.iw_state   := next_state
  io.out_uop.uopc       := next_uopc
  io.out_uop.lrs1_rtype := next_lrs1_rtype
  io.out_uop.lrs2_rtype := next_lrs2_rtype
  io.out_uop.br_mask    := next_br_mask

  //specshieldERP+ (default code commented)
  //io.out_uop.prs1_busy  := !p1
  //io.out_uop.prs2_busy  := !p2
  //io.out_uop.prs3_busy  := !p3

  //specshieldERP+ 
  io.out_uop.wake_tainted := taint
  io.out_uop.prs1_busy  := Mux(slot_uop.prs1_tainted, false.B,!p1)
  io.out_uop.prs2_busy  := Mux(slot_uop.prs2_tainted, false.B,!p2)
  io.out_uop.prs3_busy  := Mux(slot_uop.prs3_tainted, false.B,!p3)
  printf("OUT:checking for p1 pc: %x : tainted_wake_1: %d\n", 
          io.out_uop.debug_pc, slot_uop.prs1_tainted.asUInt);
  printf("OUT:checking for p2 pc: %x : tainted_wake_2: %d\n", 
          io.out_uop.debug_pc, slot_uop.prs2_tainted.asUInt);
  printf("OUT:checking for p3 pc: %x : tainted_wake_3: %d\n", 
          io.out_uop.debug_pc, slot_uop.prs3_tainted.asUInt);       


  io.out_uop.ppred_busy := !ppred
  io.out_uop.iw_p1_poisoned := p1_poisoned
  io.out_uop.iw_p2_poisoned := p2_poisoned

  //fast-bypass
  when (received_fast_bypass.asBool && (slot_uop.uopc.asUInt === 19.U)) {
    io.out_uop.fast_bypass := true.B
  }

  when (state === s_valid_2) {
    when (p1 && p2 && ppred) {
      ; // send out the entire instruction as one uop
    } .elsewhen (p1 && ppred) {
      io.uop.uopc := slot_uop.uopc
      io.uop.lrs2_rtype := RT_X
    } .elsewhen (p2 && ppred) {
      io.uop.uopc := uopSTD
      io.uop.lrs1_rtype := RT_X
    }
  }

  // debug outputs
  io.debug.p1 := p1
  io.debug.p2 := p2
  io.debug.p3 := p3
  io.debug.ppred := ppred
  io.debug.state := state
}
