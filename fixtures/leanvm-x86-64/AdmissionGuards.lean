import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import StackTable

namespace LeanVM.Admission

def rangeCmp : Kraken.Sized Directive :=
  ⟨.instr (.regular .W64 .W64 (.cmp (.reg (.low .rdx .W64)) (.imm (.int64 98)))), 7⟩

def rangeJae : Kraken.Sized Directive :=
  ⟨.instr (.regular .W64 .W64 (.jcc .ae "reject_range")), 6⟩

example : rangeCmp.directive = ⸨dir| cmpq $98, %rdx⸩ := rfl
example : rangeJae.directive = ⸨dir| jae reject_range⸩ := rfl

private def comparisonState (s : MachineData) (a b : BitVec 64) : MachineData :=
  let v := a - b
  let status := StatusFlags.from_result v {
    cf := v.unsigned != a.unsigned - b.unsigned
    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned
    of := v.signed != a.signed - b.signed }
  { s with status }

private def afterRangeCompare (s : MachineData) : MachineData :=
  comparisonState s s.regs.rdx.toBitVec 98#64

private theorem stepRangeCmp (e : Executable)
    (h : e.directivesAtAddress 0x4003d1 = [rangeCmp])
    (s : MachineData) (post : MachineState → Prop) :
    step1 e ⟨s, 0x4003d1⟩ post ↔ post ⟨afterRangeCompare s, 0x4003d8⟩ := by
  unfold step1 Executable.step
  rw [h]
  simp only [rangeCmp, Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.interp, Operand.interp, ConstExpr.interp, Effects.All]
  have dst : s.regs.get (.low .rdx .W64) = s.regs.rdx.toBitVec := by
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
  have imm : (Int64.toBitVec 98).truncate 64 = 98#64 := by decide
  have pc : (0x4003d1 : Int64) + Int64.ofNat 7 = 0x4003d8 := by decide
  rw [dst, imm, pc]
  rfl

private theorem stepRangeJae (e : Executable)
    (h : e.directivesAtAddress 0x4003d8 = [rangeJae])
    (target : e.labels.label? "reject_range" = some 0x400501)
    (s : MachineData) (post : MachineState → Prop) :
    step1 e ⟨s, 0x4003d8⟩ post ↔ post ⟨s, if s.status.cf then 0x4003de else 0x400501⟩ := by
  unfold step1 Executable.step
  rw [h]
  letI := e.labels
  change (if !s.status.cf then .resolve_label "reject_range" (fun pc => .done ⟨s, pc⟩)
    else Effects.done ⟨s, 0x4003de⟩).All post ↔
      post ⟨s, if s.status.cf then 0x4003de else 0x400501⟩
  cases s.status.cf <;> simp [Effects.All, target]

private theorem comparisonBorrows (a b : BitVec 64) :
    ((a - b).unsigned != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) := by
  have aBound := a.isLt
  have bBound := b.isLt
  by_cases h : a.toNat < b.toNat <;> simp [h, BitVec.unsigned] <;> omega

private theorem admissionRangeGuardState (e : Executable)
    (cmpAt : e.directivesAtAddress 0x4003d1 = [rangeCmp])
    (jaeAt : e.directivesAtAddress 0x4003d8 = [rangeJae])
    (rejectAt : e.labels.label? "reject_range" = some 0x400501)
    (s : MachineData) (post : MachineState → Prop) :
    step1 e ⟨s, 0x4003d1⟩ (fun mid => step1 e mid post) ↔
      post ⟨afterRangeCompare s, if 98 ≤ s.regs.rdx.toNat then 0x400501 else 0x4003de⟩ := by
  rw [stepRangeCmp e cmpAt, stepRangeJae e jaeAt rejectAt]
  change post ⟨afterRangeCompare s, if ((s.regs.rdx.toBitVec - 98#64).unsigned !=
    s.regs.rdx.toBitVec.unsigned - (98#64).unsigned) then 0x4003de else 0x400501⟩ ↔ _
  rw [comparisonBorrows, UInt64.toNat_toBitVec]
  by_cases h : s.regs.rdx.toNat < 98
  · simp [h, Nat.not_le_of_lt h]
  · simp [h, Nat.le_of_not_gt h]

theorem admissionRangeGuard (e : Executable)
    (cmpAt : e.directivesAtAddress 0x4003d1 = [rangeCmp])
    (jaeAt : e.directivesAtAddress 0x4003d8 = [rangeJae])
    (rejectAt : e.labels.label? "reject_range" = some 0x400501)
    (s : MachineData) (post : Int64 → Reg64s → Prop) :
    step1 e ⟨s, 0x4003d1⟩
      (fun mid => step1 e mid (fun out => post out.pc out.data.regs)) ↔
        post (if 98 ≤ s.regs.rdx.toNat then 0x400501 else 0x4003de) s.regs :=
  admissionRangeGuardState e cmpAt jaeAt rejectAt s (fun out => post out.pc out.data.regs)

#print axioms admissionRangeGuard

def tableLea : Kraken.Sized Directive :=
  ⟨.instr (.regular .W64 .W64
    (.lea (.low .rax .W64) ⟨some .rip, none, .int64 0x4613⟩)), 7⟩

def tableCmp : Kraken.Sized Directive :=
  ⟨.instr (.regular .W64 .W64
    (.cmp (.mem ⟨some (.reg .rax), some ⟨.rdx, .W64⟩, .int64 0⟩)
      (.imm (.int64 0x4000)))), 8⟩

def budgetJa : Kraken.Sized Directive :=
  ⟨.instr (.regular .W64 .W64 (.jcc .a "reject_input")), 6⟩

example : tableLea.directive = ⸨dir| leaq 0x4613(%rip), %rax⸩ := rfl
example : tableCmp.directive = ⸨dir| cmpq $0x4000, (%rax,%rdx,8)⸩ := rfl
example : budgetJa.directive = ⸨dir| ja reject_input⸩ := rfl

def tableEntryAddress (n : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (0x4049f8 + 8 * n)

private def afterLea (s : MachineData) : MachineData :=
  { s with regs := { s.regs with rax := 0x4049f8 } }

private theorem stepTableLea (e : Executable)
    (h : e.directivesAtAddress 0x4003de = [tableLea])
    (s : MachineData) (post : MachineState → Prop) :
    step1 e ⟨s, 0x4003de⟩ post ↔ post ⟨afterLea s, 0x4003e5⟩ := by
  unfold step1 Executable.step
  rw [h]
  rfl

private theorem addressCalculation (s : MachineData) (inRange : s.regs.rdx.toNat < 98) :
    BitVec.ofInt 64 (0x4049f8 + s.regs.rdx.toBitVec.toInt * 8) =
      tableEntryAddress s.regs.rdx.toNat := by
  have lengthInt : s.regs.rdx.toBitVec.toInt = s.regs.rdx.toNat := by
    apply BitVec.toInt_eq_toNat_of_lt
    rw [UInt64.toNat_toBitVec]
    omega
  rw [lengthInt]
  calc
    _ = BitVec.ofInt 64 ((0x4049f8 + 8 * s.regs.rdx.toNat : Nat) : Int) := by
      congr 1
      omega
    _ = _ := rfl

private theorem stepTableCmp (e : Executable)
    (h : e.directivesAtAddress 0x4003e5 = [tableCmp])
    (s : MachineData) (inRange : s.regs.rdx.toNat < 98) (entry : BitVec 64)
    (load : Mem.loadInt s.dmem (tableEntryAddress s.regs.rdx.toNat) 8 = some entry.unsigned)
    (post : MachineState → Prop) :
    step1 e ⟨afterLea s, 0x4003e5⟩ post ↔ post ⟨comparisonState (afterLea s) entry 0x4000#64, 0x4003ed⟩ := by
  unfold step1 Executable.step
  rw [h]
  simp only [tableCmp, Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.interp, Operand.interp, ConstExpr.interp, AddrExpr.interp, Effects.All,
    MachineData.load, Effects.All_require_read_access]
  simp only [Width.bits, Width.bytes, Reg64s.get64, BitVec.toAddressSize, AddressSize.address_size,
    BitVec.take, BitVec.extractLsb'_eq_self, BitVec.signed, BitVec.zeroExtend_eq_setWidth,
    BitVec.setWidth_eq]
  have base : (afterLea s).regs.rax.toBitVec.toInt = 0x4049f8 := by
    change (0x4049f8#64).toInt = 0x4049f8
    decide
  have zero : (0 : Int64).toInt = 0 := by decide
  have index : (afterLea s).regs.rdx.toBitVec.toInt = s.regs.rdx.toBitVec.toInt := rfl
  have eight : ((8 : Nat) : Int) = 8 := rfl
  have memory : (afterLea s).dmem = s.dmem := rfl
  rw [base, index, zero, Int.add_zero, eight, addressCalculation s inRange, memory, load]
  simp only [Effects.All]
  have decoded : BitVec.ofInt 64 entry.unsigned = entry := by
    rw [BitVec.unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have immediate : Int64.toBitVec 16384 = 0x4000#64 := by decide
  have pc : (0x4003e5 : Int64) + Int64.ofNat 8 = 0x4003ed := by decide
  rw [decoded, immediate, pc]
  rfl


private theorem stepBudgetJa (e : Executable)
    (h : e.directivesAtAddress 0x4003ed = [budgetJa])
    (target : e.labels.label? "reject_input" = some 0x4004fa)
    (s : MachineData) (post : MachineState → Prop) :
    step1 e ⟨s, 0x4003ed⟩ post ↔
      post ⟨s, if !s.status.cf && !s.status.zf then 0x4004fa else 0x4003f3⟩ := by
  unfold step1 Executable.step
  rw [h]
  letI := e.labels
  change (if !s.status.cf && !s.status.zf then .resolve_label "reject_input" (fun pc => .done ⟨s, pc⟩)
    else Effects.done ⟨s, 0x4003f3⟩).All post ↔ _
  cases s.status.cf <;> cases s.status.zf <;> simp [Effects.All, target]

private theorem budgetZero (entry : BitVec 64) :
    (entry - 0x4000#64 == BitVec.zero 64) = decide (entry.toNat = 0x4000) := by
  have bound := entry.isLt
  by_cases h : entry.toNat = 0x4000
  · have value : entry = 0x4000#64 := by apply BitVec.eq_of_toNat_eq; exact h
    simp [value]
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro diffZero
    have diffNat := congrArg BitVec.toNat diffZero
    simp at diffNat
    omega

theorem admissionBudgetGuard (e : Executable)
    (leaAt : e.directivesAtAddress 0x4003de = [tableLea])
    (cmpAt : e.directivesAtAddress 0x4003e5 = [tableCmp])
    (jaAt : e.directivesAtAddress 0x4003ed = [budgetJa])
    (rejectAt : e.labels.label? "reject_input" = some 0x4004fa)
    (s : MachineData) (inRange : s.regs.rdx.toNat < 98) (entry : BitVec 64)
    (load : Mem.loadInt s.dmem (tableEntryAddress s.regs.rdx.toNat) 8 = some entry.unsigned)
    (post : Int64 → UInt64 → Prop) :
    step1 e ⟨s, 0x4003de⟩
      (fun lea => step1 e lea (fun cmp => step1 e cmp (fun out => post out.pc out.data.regs.rdx))) ↔
        post (if 0x4000 < entry.toNat then 0x4004fa else 0x4003f3) s.regs.rdx := by
  rw [stepTableLea e leaAt, stepTableCmp e cmpAt s inRange entry load, stepBudgetJa e jaAt rejectAt]
  change post (if !((entry - 0x4000#64).unsigned != entry.unsigned - (0x4000#64).unsigned) &&
    !(entry - 0x4000#64 == BitVec.zero 64) then 0x4004fa else 0x4003f3) s.regs.rdx ↔ _
  rw [comparisonBorrows, budgetZero]
  by_cases h : entry.toNat < 0x4000
  · simp [h, show ¬ 0x4000 < entry.toNat by omega]
  · by_cases heq : entry.toNat = 0x4000
    · simp [heq]
    · simp [h, heq, show 0x4000 < entry.toNat by omega]

#print axioms admissionBudgetGuard

theorem provisionalAdmissionGuards (e : Executable)
    (rangeCmpAt : e.directivesAtAddress 0x4003d1 = [rangeCmp])
    (jaeAt : e.directivesAtAddress 0x4003d8 = [rangeJae])
    (rangeRejectAt : e.labels.label? "reject_range" = some 0x400501)
    (leaAt : e.directivesAtAddress 0x4003de = [tableLea])
    (tableCmpAt : e.directivesAtAddress 0x4003e5 = [tableCmp])
    (jaAt : e.directivesAtAddress 0x4003ed = [budgetJa])
    (budgetRejectAt : e.labels.label? "reject_input" = some 0x4004fa)
    (s : MachineData)
    (load : s.regs.rdx.toNat < stackTableLength →
      Mem.loadInt s.dmem (tableEntryAddress s.regs.rdx.toNat) 8 =
        some (stackRequired s.regs.rdx.toNat : Int))
    (post : Int64 → UInt64 → Prop) :
    step1 e ⟨s, 0x4003d1⟩ (fun mid => step1 e mid (fun range =>
        if range.pc = 0x4003de then
          step1 e range
            (fun lea => step1 e lea (fun cmp => step1 e cmp (fun out => post out.pc out.data.regs.rdx)))
        else post range.pc range.data.regs.rdx)) ↔
      post (if s.regs.rdx.toNat ≤ 96 then 0x4003f3
        else if s.regs.rdx.toNat < 98 then 0x4004fa else 0x400501) s.regs.rdx := by
  rw [admissionRangeGuardState e rangeCmpAt jaeAt rangeRejectAt]
  by_cases reject : 98 ≤ s.regs.rdx.toNat
  · have notSmall : ¬ s.regs.rdx.toNat ≤ 96 := by omega
    simp [reject, notSmall, Nat.not_lt.mpr reject, afterRangeCompare, comparisonState]
  · have inRange : s.regs.rdx.toNat < 98 := by omega
    have tableBound : s.regs.rdx.toNat < stackTableLength := inRange
    let entry := BitVec.ofNat 64 (stackRequired s.regs.rdx.toNat)
    have entryNat : entry.toNat = stackRequired s.regs.rdx.toNat := by
      dsimp only [entry]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      unfold stackRequired
      omega
    have loadAfter :
        Mem.loadInt (afterRangeCompare s).dmem (tableEntryAddress (afterRangeCompare s).regs.rdx.toNat) 8 =
          some entry.unsigned := by
      change Mem.loadInt s.dmem (tableEntryAddress s.regs.rdx.toNat) 8 = some (entry.toNat : Int)
      rw [entryNat]
      exact load tableBound
    simp only [ite_eq_right reject, ↓reduceIte]
    rw [admissionBudgetGuard e leaAt tableCmpAt jaAt budgetRejectAt
      (afterRangeCompare s) inRange entry loadAfter, entryNat]
    have budgetIff : stackRequired s.regs.rdx.toNat ≤ 0x4000 ↔ s.regs.rdx.toNat ≤ 96 := by
      unfold stackRequired
      omega
    by_cases admit : s.regs.rdx.toNat ≤ 96
    · have withinBudget := budgetIff.mpr admit
      simp [admit, Nat.not_lt.mpr withinBudget, afterRangeCompare, comparisonState]
    · have overBudget : 0x4000 < stackRequired s.regs.rdx.toNat :=
        Nat.lt_of_not_ge (fun withinBudget => admit (budgetIff.mp withinBudget))
      simp [admit, overBudget, inRange, afterRangeCompare, comparisonState]

#print axioms provisionalAdmissionGuards

end LeanVM.Admission
