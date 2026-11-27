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

def afterRangeCompare (s : MachineData) : MachineData :=
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

def rangeGuardSuccessor (s : MachineData) : MachineState :=
  ⟨afterRangeCompare s, if 98 ≤ s.regs.rdx.toNat then 0x400501 else 0x4003de⟩

private theorem stepRangeBranch (e : Executable)
    (jaeAt : e.directivesAtAddress 0x4003d8 = [rangeJae])
    (rejectAt : e.labels.label? "reject_range" = some 0x400501)
    (s : MachineData) (post : MachineState → Prop) :
    step1 e ⟨afterRangeCompare s, 0x4003d8⟩ post ↔ post (rangeGuardSuccessor s) := by
  rw [stepRangeJae e jaeAt rejectAt]
  unfold rangeGuardSuccessor
  change post ⟨afterRangeCompare s, if ((s.regs.rdx.toBitVec - 98#64).unsigned !=
    s.regs.rdx.toBitVec.unsigned - (98#64).unsigned) then 0x4003de else 0x400501⟩ ↔ _
  rw [comparisonBorrows, UInt64.toNat_toBitVec]
  by_cases h : s.regs.rdx.toNat < 98
  · simp [h, Nat.not_le_of_lt h]
  · simp [h, Nat.le_of_not_gt h]

theorem admissionRangeGuardState (e : Executable)
    (cmpAt : e.directivesAtAddress 0x4003d1 = [rangeCmp])
    (jaeAt : e.directivesAtAddress 0x4003d8 = [rangeJae])
    (rejectAt : e.labels.label? "reject_range" = some 0x400501)
    (s : MachineData) (post : MachineState → Prop) :
    step1 e ⟨s, 0x4003d1⟩ (fun mid => step1 e mid post) ↔
      post (rangeGuardSuccessor s) := by
  rw [stepRangeCmp e cmpAt, stepRangeBranch e jaeAt rejectAt]

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

theorem tableEntryAddressToNat (n : Nat) (inRange : n < 98) :
    (tableEntryAddress n).toNat = 0x4049f8 + 8 * n := by
  unfold tableEntryAddress
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  omega

def tableEntryReadSpan (n : Nat) (inRange : n < 98) : Std.Rco AddressBound :=
  ⟨(tableEntryAddress n).toFin.castSucc, ⟨(tableEntryAddress n).toNat + 8, by
    rw [tableEntryAddressToNat n inRange]
    change 0x4049f8 + 8 * n + 8 < 2 ^ 64 + 1
    omega⟩⟩

theorem tableEntryReadSpanBounds (n : Nat) (inRange : n < 98) :
    (tableEntryReadSpan n inRange).lower.val = 0x4049f8 + 8 * n ∧
    (tableEntryReadSpan n inRange).upper.val = 0x4049f8 + 8 * n + 8 := by
  change (tableEntryAddress n).toNat = _ ∧ (tableEntryAddress n).toNat + 8 = _
  rw [tableEntryAddressToNat n inRange]
  exact ⟨rfl, rfl⟩

def afterLea (s : MachineData) : MachineData :=
  { s with regs := { s.regs with rax := 0x4049f8 } }

def afterBudgetCompare (s : MachineData) (entry : BitVec 64) : MachineData :=
  comparisonState (afterLea s) entry 0x4000#64

def budgetGuardSuccessor (s : MachineData) (entry : BitVec 64) : MachineState :=
  ⟨afterBudgetCompare s entry, if 0x4000 < entry.toNat then 0x4004fa else 0x4003f3⟩

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

theorem tableCmpReadStep (e : Executable)
    (h : e.directivesAtAddress 0x4003e5 = [tableCmp])
    (s : MachineData) (inRange : s.regs.rdx.toNat < 98) (entry : BitVec 64)
    (load : Mem.loadInt s.dmem (tableEntryAddress s.regs.rdx.toNat) 8 = some entry.unsigned) :
    e.step ⟨afterLea s, 0x4003e5⟩ .done =
      .require_exec_access ⟨0x4003e5, 0x4003ed⟩
        (fun () => .require_read_access (tableEntryReadSpan s.regs.rdx.toNat inRange)
          (fun () => .done ⟨afterBudgetCompare s entry, 0x4003ed⟩)) := by
  unfold Executable.step
  rw [h]
  simp only [tableCmp, Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.interp, Operand.interp, ConstExpr.interp, AddrExpr.interp, MachineData.load]
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
  dsimp only
  have decoded : BitVec.ofInt 64 entry.unsigned = entry := by
    rw [BitVec.unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have immediate : Int64.toBitVec 16384 = 0x4000#64 := by decide
  have pc : (0x4003e5 : Int64) + Int64.ofNat 8 = 0x4003ed := by decide
  rw [decoded, immediate, pc]
  have noWrap : ((tableEntryAddress s.regs.rdx.toNat).toFin.castSucc : AddressBound).val +
      (UInt64.ofNat 8).toNat ≤ UInt64.size := by
    change (tableEntryAddress s.regs.rdx.toNat).toNat + 8 ≤ UInt64.size
    rw [tableEntryAddressToNat _ inRange]
    change 0x4049f8 + 8 * s.regs.rdx.toNat + 8 ≤ 2 ^ 64
    omega
  simp only [require_access, dite_eq_left noWrap]
  rfl

private theorem stepTableCmp (e : Executable)
    (h : e.directivesAtAddress 0x4003e5 = [tableCmp])
    (s : MachineData) (inRange : s.regs.rdx.toNat < 98) (entry : BitVec 64)
    (load : Mem.loadInt s.dmem (tableEntryAddress s.regs.rdx.toNat) 8 = some entry.unsigned)
    (post : MachineState → Prop) :
    step1 e ⟨afterLea s, 0x4003e5⟩ post ↔ post ⟨afterBudgetCompare s entry, 0x4003ed⟩ := by
  unfold step1
  rw [tableCmpReadStep e h s inRange entry load]
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

private theorem stepBudgetBranch (e : Executable)
    (jaAt : e.directivesAtAddress 0x4003ed = [budgetJa])
    (rejectAt : e.labels.label? "reject_input" = some 0x4004fa)
    (s : MachineData) (entry : BitVec 64) (post : MachineState → Prop) :
    step1 e ⟨afterBudgetCompare s entry, 0x4003ed⟩ post ↔
      post (budgetGuardSuccessor s entry) := by
  rw [stepBudgetJa e jaAt rejectAt]
  unfold budgetGuardSuccessor
  change post ⟨afterBudgetCompare s entry,
    if !((entry - 0x4000#64).unsigned != entry.unsigned - (0x4000#64).unsigned) &&
      !(entry - 0x4000#64 == BitVec.zero 64) then 0x4004fa else 0x4003f3⟩ ↔ _
  rw [comparisonBorrows, budgetZero]
  by_cases h : entry.toNat < 0x4000
  · simp [h, show ¬ 0x4000 < entry.toNat by omega]
  · by_cases heq : entry.toNat = 0x4000
    · simp [heq]
    · simp [h, heq, show 0x4000 < entry.toNat by omega]

theorem admissionBudgetGuardState (e : Executable)
    (leaAt : e.directivesAtAddress 0x4003de = [tableLea])
    (cmpAt : e.directivesAtAddress 0x4003e5 = [tableCmp])
    (jaAt : e.directivesAtAddress 0x4003ed = [budgetJa])
    (rejectAt : e.labels.label? "reject_input" = some 0x4004fa)
    (s : MachineData) (inRange : s.regs.rdx.toNat < 98) (entry : BitVec 64)
    (load : Mem.loadInt s.dmem (tableEntryAddress s.regs.rdx.toNat) 8 = some entry.unsigned)
    (post : MachineState → Prop) :
    step1 e ⟨s, 0x4003de⟩ (fun lea => step1 e lea (fun cmp => step1 e cmp post)) ↔
      post (budgetGuardSuccessor s entry) := by
  rw [stepTableLea e leaAt, stepTableCmp e cmpAt s inRange entry load,
    stepBudgetBranch e jaAt rejectAt]

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
        post (if 0x4000 < entry.toNat then 0x4004fa else 0x4003f3) s.regs.rdx :=
  admissionBudgetGuardState e leaAt cmpAt jaAt rejectAt s inRange entry load
    (fun out => post out.pc out.data.regs.rdx)

#print axioms admissionBudgetGuard

def provisionalBudgetEntry (n : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (stackRequired n)

theorem provisionalBudgetEntryToNat (n : Nat) (inRange : n < 98) :
    (provisionalBudgetEntry n).toNat = stackRequired n := by
  unfold provisionalBudgetEntry
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  unfold stackRequired
  omega

def provisionalAdmissionSuccessor (s : MachineData) : MachineState :=
  if s.regs.rdx.toNat < 98 then
    budgetGuardSuccessor (afterRangeCompare s) (provisionalBudgetEntry s.regs.rdx.toNat)
  else
    rangeGuardSuccessor s

theorem provisionalAdmissionSuccessorPc (s : MachineData) :
    (provisionalAdmissionSuccessor s).pc = if s.regs.rdx.toNat ≤ 96 then 0x4003f3
      else if s.regs.rdx.toNat < 98 then 0x4004fa else 0x400501 := by
  by_cases inRange : s.regs.rdx.toNat < 98
  · have budgetIff : 0x4000 < stackRequired s.regs.rdx.toNat ↔ 96 < s.regs.rdx.toNat := by
      unfold stackRequired
      omega
    simp only [provisionalAdmissionSuccessor, ite_eq_left inRange, budgetGuardSuccessor,
      provisionalBudgetEntryToNat _ inRange, budgetIff]
    by_cases admit : s.regs.rdx.toNat ≤ 96
    · simp [admit, Nat.not_lt.mpr admit]
    · simp [Nat.lt_of_not_ge admit, admit]
  · have reject := Nat.le_of_not_gt inRange
    have notSmall : ¬ s.regs.rdx.toNat ≤ 96 := by omega
    simp [provisionalAdmissionSuccessor, inRange, rangeGuardSuccessor, reject, notSmall]

theorem provisionalAdmissionSuccessorInRange (s : MachineData) (inRange : s.regs.rdx.toNat < 98) :
    provisionalAdmissionSuccessor s =
      ⟨afterBudgetCompare (afterRangeCompare s) (provisionalBudgetEntry s.regs.rdx.toNat),
        if s.regs.rdx.toNat ≤ 96 then 0x4003f3 else 0x4004fa⟩ := by
  have pc := provisionalAdmissionSuccessorPc s
  simp only [ite_eq_left inRange, provisionalAdmissionSuccessor] at pc ⊢
  exact congrArg (fun addr => ⟨afterBudgetCompare (afterRangeCompare s)
    (provisionalBudgetEntry s.regs.rdx.toNat), addr⟩ : Int64 → MachineState) pc

theorem provisionalAdmissionSuccessorAdmitted (s : MachineData) (admit : s.regs.rdx.toNat ≤ 96) :
    provisionalAdmissionSuccessor s =
      ⟨afterBudgetCompare (afterRangeCompare s) (provisionalBudgetEntry s.regs.rdx.toNat), 0x4003f3⟩ := by
  have inRange : s.regs.rdx.toNat < 98 := by omega
  rw [provisionalAdmissionSuccessorInRange s inRange, ite_eq_left admit]

theorem provisionalAdmissionSuccessorRejectedRange (s : MachineData) (reject : 98 ≤ s.regs.rdx.toNat) :
    provisionalAdmissionSuccessor s = ⟨afterRangeCompare s, 0x400501⟩ := by
  simp [provisionalAdmissionSuccessor, rangeGuardSuccessor, Nat.not_lt.mpr reject, reject]

theorem provisionalAdmissionSuccessorFrame (s : MachineData) :
    (provisionalAdmissionSuccessor s).data.regs =
      (if s.regs.rdx.toNat < 98 then { s.regs with rax := 0x4049f8 } else s.regs) ∧
    (provisionalAdmissionSuccessor s).data.zmms = s.zmms ∧
    (provisionalAdmissionSuccessor s).data.df = s.df ∧
    (provisionalAdmissionSuccessor s).data.dmem = s.dmem := by
  by_cases inRange : s.regs.rdx.toNat < 98 <;>
    simp [inRange, provisionalAdmissionSuccessor, rangeGuardSuccessor, budgetGuardSuccessor,
      afterBudgetCompare, afterRangeCompare, afterLea, comparisonState]

theorem provisionalAdmissionSuccessorRdx (s : MachineData) :
    (provisionalAdmissionSuccessor s).data.regs.rdx = s.regs.rdx := by
  rw [(provisionalAdmissionSuccessorFrame s).1]
  split <;> rfl

private theorem loadAfterRangeCompare (s : MachineData) (inRange : s.regs.rdx.toNat < 98)
    (load : s.regs.rdx.toNat < stackTableLength →
      Mem.loadInt s.dmem (tableEntryAddress s.regs.rdx.toNat) 8 =
        some (stackRequired s.regs.rdx.toNat : Int)) :
    Mem.loadInt (afterRangeCompare s).dmem (tableEntryAddress (afterRangeCompare s).regs.rdx.toNat) 8 =
      some (provisionalBudgetEntry s.regs.rdx.toNat).unsigned := by
  change Mem.loadInt s.dmem (tableEntryAddress s.regs.rdx.toNat) 8 =
    some ((provisionalBudgetEntry s.regs.rdx.toNat).toNat : Int)
  rw [provisionalBudgetEntryToNat _ inRange]
  exact load inRange

private theorem provisionalAdmissionGuardsState (e : Executable)
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
    (post : MachineState → Prop) :
    step1 e ⟨s, 0x4003d1⟩ (fun mid => step1 e mid (fun range =>
      if range.pc = 0x4003de then
        step1 e range (fun lea => step1 e lea (fun cmp => step1 e cmp post))
      else post range)) ↔ post (provisionalAdmissionSuccessor s) := by
  rw [admissionRangeGuardState e rangeCmpAt jaeAt rangeRejectAt]
  by_cases inRange : s.regs.rdx.toNat < 98
  · simp only [rangeGuardSuccessor, provisionalAdmissionSuccessor,
      ite_eq_right (Nat.not_le_of_lt inRange), ite_eq_left inRange, ↓reduceIte]
    exact admissionBudgetGuardState e leaAt tableCmpAt jaAt budgetRejectAt (afterRangeCompare s)
      inRange (provisionalBudgetEntry s.regs.rdx.toNat) (loadAfterRangeCompare s inRange load) post
  · simp [provisionalAdmissionSuccessor, inRange, rangeGuardSuccessor, Nat.le_of_not_gt inRange]

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
  simpa only [provisionalAdmissionSuccessorPc, provisionalAdmissionSuccessorRdx] using
    (provisionalAdmissionGuardsState e rangeCmpAt jaeAt rangeRejectAt leaAt tableCmpAt jaAt
      budgetRejectAt s load (fun out => post out.pc out.data.regs.rdx))

private theorem eventuallyFromStep (e : Executable) (before after : MachineState)
    (step : ∀ midPost, step1 e before midPost ↔ midPost after)
    (post : MachineState → Prop)
    (continueFrom : Eventually (step1 e) post after) :
    Eventually (step1 e) post before :=
  .step before (· = after) ((step _).mpr rfl) (fun _ h => h ▸ continueFrom)

theorem provisionalAdmissionEventually (e : Executable)
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
    (post : MachineState → Prop)
    (continueFrom : Eventually (step1 e) post (provisionalAdmissionSuccessor s)) :
    Eventually (step1 e) post ⟨s, 0x4003d1⟩ := by
  apply eventuallyFromStep e _ _ (stepRangeCmp e rangeCmpAt s) post
  apply eventuallyFromStep e _ _ (stepRangeBranch e jaeAt rangeRejectAt s) post
  by_cases inRange : s.regs.rdx.toNat < 98
  · have fallthrough : rangeGuardSuccessor s = ⟨afterRangeCompare s, 0x4003de⟩ := by
      simp [rangeGuardSuccessor, Nat.not_le_of_lt inRange]
    rw [fallthrough]
    apply eventuallyFromStep e _ _ (stepTableLea e leaAt (afterRangeCompare s)) post
    let entry := provisionalBudgetEntry s.regs.rdx.toNat
    apply eventuallyFromStep e _ _
      (stepTableCmp e tableCmpAt (afterRangeCompare s) inRange entry
        (loadAfterRangeCompare s inRange load)) post
    apply eventuallyFromStep e _ _ (stepBudgetBranch e jaAt budgetRejectAt (afterRangeCompare s) entry) post
    simpa only [provisionalAdmissionSuccessor, ite_eq_left inRange] using continueFrom
  · simpa only [provisionalAdmissionSuccessor, ite_eq_right inRange] using continueFrom

#print axioms tableCmpReadStep
#print axioms tableEntryReadSpanBounds
#print axioms provisionalAdmissionGuards
#print axioms provisionalAdmissionEventually

end LeanVM.Admission
