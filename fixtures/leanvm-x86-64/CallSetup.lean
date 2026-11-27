import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import AdmissionGuards

namespace LeanVM.Admission

def callSetupCode : List (Int64 × Kraken.Sized Directive) :=
  [ (0x4003f3, ⟨⸨dir| leaq 0x4c0e(%rip), %rdi⸩, 7⟩)
  , (0x4003fa, ⟨⸨dir| movq (%r12), %rsi⸩, 4⟩)
  , (0x4003fe, ⟨⸨dir| movq %r12, 0x4c23(%rip)⸩, 7⟩)
  , (0x400405, ⟨⸨dir| movq %r13, %rsp⸩, 3⟩)
  , (0x400408, ⟨⸨dir| movq $0x1122334455667788, %rbx⸩, 10⟩)
  , (0x400412, ⟨⸨dir| movq $0x2233445566778899, %rbp⸩, 10⟩)
  , (0x40041c, ⟨⸨dir| movq $0x33445566778899aa, %r12⸩, 10⟩)
  , (0x400426, ⟨⸨dir| movq $0x445566778899aabb, %r13⸩, 10⟩)
  , (0x400430, ⟨⸨dir| movq $0x5566778899aabbcc, %r14⸩, 10⟩)
  , (0x40043a, ⟨⸨dir| movq $0x66778899aabbccdd, %r15⸩, 10⟩)
  , (0x400444, ⟨.instr (.regular .W64 .W64 (.call (.rel (.int64 (-0x329))))), 5⟩) ]

def callSetupAt (e : Executable) : Prop :=
  ∀ addr instr, (addr, instr) ∈ callSetupCode → e.directivesAtAddress addr = [instr]

def callSetupSuccessor (s : MachineData) (input : BitVec 64) : MachineState :=
  ⟨{ s with
      regs := { s.regs with
        rdi := 0x405008
        rsi := UInt64.ofBitVec input
        rsp := 0x10010ff8
        rbx := 0x1122334455667788
        rbp := 0x2233445566778899
        r12 := 0x33445566778899aa
        r13 := 0x445566778899aabb
        r14 := 0x5566778899aabbcc
        r15 := 0x66778899aabbccdd }
      dmem := (s.dmem.storeInt 0x405028#64 8 s.regs.r12.toBitVec.toInt).storeInt
        0x10010ff8#64 8 0x400449 }, 0x400120⟩

private theorem advance {e : Executable} {post : MachineState → Prop} {s t : MachineState}
    (step : step1 e s (· = t)) (next : Eventually (step1 e) post t) :
    Eventually (step1 e) post s :=
  .step s (· = t) step (fun _ eq => eq ▸ next)

private theorem knownStepEffects {e : Executable} (code : callSetupAt e)
    (i : Nat) (hi : i < callSetupCode.length) (s : MachineData) :
    e.step ⟨s, callSetupCode[i].1⟩ .done =
      letI := e.labels
      Directives.interp [callSetupCode[i].2] s callSetupCode[i].1
        (fun pc s' => .done ⟨s', pc⟩) := by
  have atPC := code (callSetupCode[i].1) (callSetupCode[i].2) (List.getElem_mem hi)
  simp only [Executable.step, atPC]

private theorem knownStep {e : Executable} (code : callSetupAt e)
    (i : Nat) (hi : i < callSetupCode.length) (s : MachineData) (post : MachineState → Prop) :
    step1 e ⟨s, callSetupCode[i].1⟩ post ↔
      letI := e.labels
      (Directives.interp [callSetupCode[i].2] s callSetupCode[i].1
        (fun pc s' => .done ⟨s', pc⟩)).All post := by
  unfold step1
  rw [knownStepEffects code i hi s]


theorem caseInputReadStep (e : Executable) (code : callSetupAt e) (s : MachineData)
    (input : BitVec 64) (read : s.dmem.loadInt s.regs.r12.toBitVec 8 = some input.unsigned) :
    e.step ⟨s, 0x4003fa⟩ .done =
      .require_exec_access ⟨0x4003fa, 0x4003fe⟩ (fun () =>
        require_access .require_read_access s.regs.r12.toBitVec 8 (fun () =>
          .done ⟨{ s with regs := { s.regs with rsi := UInt64.ofBitVec input } }, 0x4003fe⟩)) := by
  change e.step ⟨s, callSetupCode[1].1⟩ .done = _
  rw [knownStepEffects code 1 (by decide) s]
  simp only [callSetupCode, List.getElem_cons_succ, List.getElem_cons_zero,
    Directives.interp, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, AddrExpr.interp, ConstExpr.interp, MachineData.load]
  simp only [Width.bits, Width.bytes, Reg64s.get64, BitVec.toAddressSize, AddressSize.address_size,
    BitVec.signed, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq, Int.add_zero]
  have zero : (0 : Int64).toInt = 0 := by decide
  rw [zero, Int.add_zero, BitVec.ofInt_toInt]
  simp only [BitVec.take, BitVec.extractLsb'_eq_self]
  rw [read]
  have decode : BitVec.ofInt 64 input.unsigned = input := by
    rw [BitVec.unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [decode]
  rfl

#print axioms caseInputReadStep

theorem selectedCaseWriteStep (e : Executable) (code : callSetupAt e) (s : MachineData)
    (oldValue : Int) (mapped : s.dmem.loadInt 0x405028#64 8 = some oldValue) :
    e.step ⟨s, 0x4003fe⟩ .done =
      .require_exec_access ⟨0x4003fe, 0x400405⟩ (fun () =>
        .require_write_access ⟨0x405028, 0x405030⟩ (fun () =>
          .done ⟨{ s with dmem := s.dmem.storeInt 0x405028#64 8 s.regs.r12.toBitVec.toInt },
            0x400405⟩)) := by
  change e.step ⟨s, callSetupCode[2].1⟩ .done = _
  rw [knownStepEffects code 2 (by decide) s]
  simp only [callSetupCode, List.getElem_cons_succ, List.getElem_cons_zero,
    Directives.interp, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, AddrExpr.interp, ConstExpr.interp, MachineData.set, MachineData.store]
  have address : BitVec.zeroExtend 64 (BitVec.ofInt Width.W64.bits
      (((0x4003fe : Int64) + Int64.ofNat 7).toInt + 0 + (0x4c23 : Int64).toInt)) =
        0x405028#64 := by decide
  have source : s.regs.get (.low .r12 .W64) = s.regs.r12.toBitVec := by
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
  rw [address, source]
  simp only [Width.bytes, mapped]
  rfl

theorem returnAddressWriteStep (e : Executable) (code : callSetupAt e) (s : MachineData)
    (stackTop : s.regs.rsp = 0x10011000)
    (oldValue : Int) (mapped : s.dmem.loadInt 0x10010ff8#64 8 = some oldValue) :
    e.step ⟨s, 0x400444⟩ .done =
      .require_exec_access ⟨0x400444, 0x400449⟩ (fun () =>
        .require_write_access ⟨0x10010ff8, 0x10011000⟩ (fun () =>
          .done ⟨{ s with
            regs := { s.regs with rsp := 0x10010ff8 }
            dmem := s.dmem.storeInt 0x10010ff8#64 8 0x400449 }, 0x400120⟩)) := by
  change e.step ⟨s, callSetupCode[10].1⟩ .done = _
  rw [knownStepEffects code 10 (by decide) s]
  simp only [callSetupCode, List.getElem_cons_succ, List.getElem_cons_zero,
    Directives.interp, Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store]
  have entryStack : s.regs.get64 .rsp - Width.W64.bytesv = 0x10010ff8#64 := by
    change s.regs.rsp.toBitVec - 8#64 = 0x10010ff8#64
    rw [stackTop]
    decide
  simp only [entryStack, Width.bytes, mapped]
  rfl

#print axioms selectedCaseWriteStep
#print axioms returnAddressWriteStep

private theorem storeKeepsByte (m : Mem 64) (start address : BitVec 64) (value : Int)
    (outside : 8 ≤ (address - start).toNat) :
    (m.storeInt start 8 value).get? address = m.get? address := by
  change (m ∪ (Int.toBytes 8 value).At start)[address]? = m[address]?
  rw [Std.ExtHashMap.getElem?_union, get?_At]
  · rw [List.getElem?_eq_none (by simpa [Int.toBytes_length] using outside)]
    rfl
  · simp [Int.toBytes_length]

theorem callSetupPreservesImageDataByte (s : MachineData) (input : BitVec 64) (address : BitVec 64)
    (belowWritableLoad : address.toNat < 0x405000) :
    (callSetupSuccessor s input).data.dmem.get? address = s.dmem.get? address := by
  have outsideSelectedCase : 8 ≤ (address - 0x405028#64).toNat := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have outsideReturnSlot : 8 ≤ (address - 0x10010ff8#64).toNat := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  change ((s.dmem.storeInt 0x405028#64 8 s.regs.r12.toBitVec.toInt).storeInt
    0x10010ff8#64 8 0x400449).get? address = s.dmem.get? address
  rw [storeKeepsByte _ _ _ _ outsideReturnSlot, storeKeepsByte _ _ _ _ outsideSelectedCase]

#print axioms callSetupPreservesImageDataByte

private theorem selectedStorePreservesReturnSlot (m : Mem 64) (v : Int) :
    (m.storeInt 0x405028#64 8 v).loadInt 0x10010ff8#64 8 = m.loadInt 0x10010ff8#64 8 := by
  simp only [Mem.loadInt, Mem.loadBytes]
  congr 2
  apply List.map_congr_left
  intro i hi
  apply storeKeepsByte
  have below : i < 8 := List.mem_range.mp hi
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem callSetupEventually (e : Executable) (code : callSetupAt e)
    (s : MachineData) (input : BitVec 64) (stackTop : s.regs.r13 = 0x10011000)
    (caseRead : s.dmem.loadInt s.regs.r12.toBitVec 8 = some input.unsigned)
    (savedCase ra : Int)
    (selectedMapped : s.dmem.loadInt 0x405028#64 8 = some savedCase)
    (retMapped : s.dmem.loadInt 0x10010ff8#64 8 = some ra)
    (post : MachineState → Prop)
    (continueFrom : Eventually (step1 e) post (callSetupSuccessor s input)) :
    Eventually (step1 e) post ⟨s, 0x4003f3⟩ := by
  let rd := { s with regs := { s.regs with rdi := 0x405008 } }
  refine advance (t := ⟨rd, 0x4003fa⟩) ?_ ?_
  · exact (knownStep code 0 (by decide) s _).mpr rfl
  let args := { rd with regs := { rd.regs with rsi := UInt64.ofBitVec input } }
  refine advance (t := ⟨args, 0x4003fe⟩) ?_ ?_
  · unfold step1
    rw [caseInputReadStep e code rd input caseRead]
    simp only [Effects.All, Effects.All_require_read_access]
    rfl
  let selected := {args with dmem := s.dmem.storeInt 0x405028#64 8 s.regs.r12.toBitVec.toInt}
  refine advance (t := ⟨selected, 0x400405⟩) ?_ ?_
  · unfold step1
    rw [selectedCaseWriteStep e code args savedCase selectedMapped]
    rfl
  let switched := {selected with regs := { selected.regs with rsp := 0x10011000 } }
  refine advance (t := ⟨switched, 0x400408⟩) ?_ ?_
  · apply (knownStep code 3 (by decide) selected _).mpr
    have top : selected.regs.r13 = 0x10011000 := stackTop
    simp only [callSetupCode, List.getElem_cons_succ, List.getElem_cons_zero,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, Effects.All, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, top]
    rfl
  let saveBX := {switched with regs := { switched.regs with rbx := 0x1122334455667788 } }
  refine advance (t := ⟨saveBX, 0x400412⟩) ?_ ?_
  · exact (knownStep code 4 (by decide) switched _).mpr rfl
  let saveBP := {saveBX with regs := { saveBX.regs with rbp := 0x2233445566778899 } }
  refine advance (t := ⟨saveBP, 0x40041c⟩) ?_ ?_
  · exact (knownStep code 5 (by decide) saveBX _).mpr rfl
  let save12 := {saveBP with regs := { saveBP.regs with r12 := 0x33445566778899aa } }
  refine advance (t := ⟨save12, 0x400426⟩) ?_ ?_
  · exact (knownStep code 6 (by decide) saveBP _).mpr rfl
  let save13 := {save12 with regs := { save12.regs with r13 := 0x445566778899aabb } }
  refine advance (t := ⟨save13, 0x400430⟩) ?_ ?_
  · exact (knownStep code 7 (by decide) save12 _).mpr rfl
  let save14 := {save13 with regs := { save13.regs with r14 := 0x5566778899aabbcc } }
  refine advance (t := ⟨save14, 0x40043a⟩) ?_ ?_
  · exact (knownStep code 8 (by decide) save13 _).mpr rfl
  let save15 := {save14 with regs := { save14.regs with r15 := 0x66778899aabbccdd } }
  refine advance (t := ⟨save15, 0x400444⟩) ?_ ?_
  · exact (knownStep code 9 (by decide) save14 _).mpr rfl
  refine advance (t := callSetupSuccessor s input) ?_ continueFrom
  have stillMapped : save15.dmem.loadInt 0x10010ff8#64 8 = some ra := by
    change (s.dmem.storeInt 0x405028#64 8 s.regs.r12.toBitVec.toInt).loadInt 0x10010ff8#64 8 = some ra
    rw [selectedStorePreservesReturnSlot, retMapped]
  have switchedStack : save15.regs.rsp = 0x10011000 := rfl
  unfold step1
  rw [returnAddressWriteStep e code save15 switchedStack ra stillMapped]
  rfl

#print axioms callSetupEventually

theorem callSetupEntryStack (s : MachineData) (input : BitVec 64) :
    (callSetupSuccessor s input).data.regs.rsp = 0x10010ff8 ∧
    (callSetupSuccessor s input).data.regs.rsp.toNat % 16 = 8 := by
  change (0x10010ff8 : UInt64) = 0x10010ff8 ∧ (0x10010ff8 : UInt64).toNat % 16 = 8
  decide

theorem callSetupReturnSlot (s : MachineData) (input : BitVec 64) :
    (callSetupSuccessor s input).data.dmem.loadInt 0x10010ff8#64 8 = some 0x400449 := by
  let initial := s.dmem.storeInt 0x405028#64 8 s.regs.r12.toBitVec.toInt
  change (initial.storeInt 0x10010ff8#64 8 0x400449).loadInt 0x10010ff8#64 8 = some 0x400449
  unfold Mem.loadInt Mem.loadBytes
  have lookups :
      ((List.range 8).map fun i =>
        (initial.storeInt 0x10010ff8#64 8 0x400449).get?
          (0x10010ff8#64 + BitVec.ofNat 64 i)) =
        (List.range 8).map fun i => (Int.toBytes 8 0x400449)[i]? := by
    apply List.map_congr_left
    intro i hi
    have inRange : i < 8 := List.mem_range.mp hi
    have written := get?_At_idx (Int.toBytes 8 0x400449) 0x10010ff8#64 i
      (by omega) (by simp [Int.toBytes_length])
    simp only [Std.ExtHashMap.get?_eq_getElem?] at written
    change (initial ∪ (Int.toBytes 8 0x400449).At 0x10010ff8#64)[0x10010ff8#64 + BitVec.ofNat 64 i]? = _
    rw [Std.ExtHashMap.getElem?_union, written, List.getElem?_eq_getElem (by simpa [Int.toBytes_length] using inRange)]
    rfl
  rw [lookups]
  decide

theorem admissionThenCall (e : Executable)
    (rangeCmpAt : e.directivesAtAddress 0x4003d1 = [rangeCmp])
    (jaeAt : e.directivesAtAddress 0x4003d8 = [rangeJae])
    (rangeRejectAt : e.labels.label? "reject_range" = some 0x400501)
    (leaAt : e.directivesAtAddress 0x4003de = [tableLea])
    (tableCmpAt : e.directivesAtAddress 0x4003e5 = [tableCmp])
    (jaAt : e.directivesAtAddress 0x4003ed = [budgetJa])
    (budgetRejectAt : e.labels.label? "reject_input" = some 0x4004fa)
    (setupAt : callSetupAt e) (s : MachineData) (admitted : s.regs.rdx.toNat ≤ 96)
    (tableLoad : s.regs.rdx.toNat < stackTableLength →
      Mem.loadInt s.dmem (tableEntryAddress s.regs.rdx.toNat) 8 =
        some (stackRequired s.regs.rdx.toNat : Int))
    (input : BitVec 64) (stackTop : s.regs.r13 = 0x10011000)
    (caseRead : s.dmem.loadInt s.regs.r12.toBitVec 8 = some input.unsigned)
    (savedCase ra : Int)
    (selectedMapped : s.dmem.loadInt 0x405028#64 8 = some savedCase)
    (retMapped : s.dmem.loadInt 0x10010ff8#64 8 = some ra)
    (post : MachineState → Prop)
    (continueFrom : Eventually (step1 e) post
      (callSetupSuccessor (provisionalAdmissionSuccessor s).data input)) :
    Eventually (step1 e) post ⟨s, 0x4003d1⟩ := by
  apply provisionalAdmissionEventually e rangeCmpAt jaeAt rangeRejectAt leaAt tableCmpAt jaAt
    budgetRejectAt s tableLoad post
  let successor := provisionalAdmissionSuccessor s
  have pc : successor.pc = 0x4003f3 := by
    simp [successor, provisionalAdmissionSuccessorPc, admitted]
  have inRange : s.regs.rdx.toNat < 98 := by omega
  have frame := provisionalAdmissionSuccessorFrame s
  have regs : successor.data.regs = { s.regs with rax := 0x4049f8 } := by
    simpa only [successor, ite_eq_left inRange] using frame.1
  have memory : successor.data.dmem = s.dmem := frame.2.2.2
  have topAfter : successor.data.regs.r13 = 0x10011000 := by
    simpa only [regs] using stackTop
  have inputAfter : successor.data.dmem.loadInt successor.data.regs.r12.toBitVec 8 =
      some input.unsigned := by
    simpa only [memory, regs] using caseRead
  have selectedAfter : successor.data.dmem.loadInt 0x405028#64 8 = some savedCase := by
    simpa only [memory] using selectedMapped
  have retAfter : successor.data.dmem.loadInt 0x10010ff8#64 8 = some ra := by
    simpa only [memory] using retMapped
  have run := callSetupEventually e setupAt successor.data input topAfter inputAfter
    savedCase ra selectedAfter retAfter post continueFrom
  change Eventually (step1 e) post ⟨successor.data, successor.pc⟩
  rw [pc]
  exact run

#print axioms callSetupEntryStack
#print axioms callSetupReturnSlot
#print axioms admissionThenCall

end LeanVM.Admission
