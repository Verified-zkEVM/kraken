import CaseArgumentBridge

namespace LeanVM.Admission

def selectCaseLea : Kraken.Sized Directive :=
  ⟨⸨dir| leaq 0x2c3b(%rip), %r12⸩, 7⟩

def selectCaseShift : Kraken.Sized Directive :=
  ⟨⸨dir| shlq $5, %rbx⸩, 4⟩

def selectCaseAdd : Kraken.Sized Directive :=
  ⟨⸨dir| addq %rbx, %r12⸩, 3⟩

def selectCaseLength : Kraken.Sized Directive :=
  ⟨⸨dir| movq 8(%r12), %rdx⸩, 5⟩

structure StockCaseSelectionAt (e : Executable) : Prop where
  lea : e.directivesAtAddress 0x4003be = [selectCaseLea]
  shift : e.directivesAtAddress 0x4003c5 = [selectCaseShift]
  add : e.directivesAtAddress 0x4003c9 = [selectCaseAdd]
  length : e.directivesAtAddress 0x4003cc = [selectCaseLength]

private def afterSelectCaseLea (s : MachineData) : MachineData :=
  { s with regs := { s.regs with r12 := 0x403000 } }

private def afterSelectCaseShift (s : MachineData) (af of : Bool) : MachineData :=
  let result := s.regs.rbx.toBitVec <<< (5 : Nat)
  { s with
    regs := { s.regs with rbx := UInt64.ofBitVec result }
    status := .from_result result { cf := (s.regs.rbx.toBitVec <<< (4 : Nat)).msb, af, of } }

private def afterSelectCaseAdd (s : MachineData) : MachineData :=
  let a := s.regs.rbx.toBitVec
  let b := s.regs.r12.toBitVec
  let result := a + b
  { s with
    regs := { s.regs with r12 := UInt64.ofBitVec result }
    status := .from_result result {
      cf := result.unsigned != a.unsigned + b.unsigned
      af := (result.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned
      of := result.signed != a.signed + b.signed } }

private theorem selectCaseLeaStep (e : Executable) (code : StockCaseSelectionAt e)
    (s : MachineData) (post : MachineState → Prop) :
    step1 e ⟨s, 0x4003be⟩ post ↔ post ⟨afterSelectCaseLea s, 0x4003c5⟩ := by
  unfold step1 Executable.step
  rw [code.lea]
  rfl

private theorem selectCaseShiftEffects (e : Executable) (code : StockCaseSelectionAt e)
    (s : MachineData) :
    e.step ⟨s, 0x4003c5⟩ .done =
      .require_exec_access ⟨0x4003c5, 0x4003c9⟩ (fun () =>
        undefined fun af : Bool => undefined fun of : Bool =>
          .done ⟨afterSelectCaseShift s af of, 0x4003c9⟩) := by
  unfold Executable.step
  rw [code.shift]
  simp only [selectCaseShift, Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, ShiftCountExpr.interpMasked,
    ShiftCountExpr.interp, ConstExpr.interp]
  have rbx : s.regs.get (.low .rbx .W64) = s.regs.rbx.toBitVec := by
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
  rw [rbx]
  rfl

private theorem selectCaseAddStep (e : Executable) (code : StockCaseSelectionAt e)
    (s : MachineData) (post : MachineState → Prop) :
    step1 e ⟨s, 0x4003c9⟩ post ↔ post ⟨afterSelectCaseAdd s, 0x4003cc⟩ := by
  unfold step1 Executable.step
  rw [code.add]
  simp only [selectCaseAdd, Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg]
  have rbx : s.regs.get (.low .rbx .W64) = s.regs.rbx.toBitVec := by
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
  have r12 : s.regs.get (.low .r12 .W64) = s.regs.r12.toBitVec := by
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
  rw [rbx, r12]
  rfl

def stockCaseLengthReadSpan (index : Fin stockCaseArguments.length) : Std.Rco AddressBound :=
  ⟨(stockCaseRecordAddress index + 8#64).toFin.castSucc,
    ⟨(stockCaseRecordAddress index + 8#64).toNat + 8, by
      have bound := (stockCaseArgumentSpan index).2.1
      change (stockCaseRecordAddress index + 8#64).toNat + 8 < 2 ^ 64 + 1
      rw [(stockCaseArgumentSpan index).2.2.2]
      omega⟩⟩

theorem stockCaseLengthReadSpanBounds (index : Fin stockCaseArguments.length) :
    (stockCaseLengthReadSpan index).lower.val = 0x403000 + 32 * index.val + 8 ∧
    (stockCaseLengthReadSpan index).upper.val = 0x403000 + 32 * index.val + 16 := by
  have bound : index.val < 11 := index.isLt
  have address : (stockCaseRecordAddress index).toNat = 0x403000 + 32 * index.val := by
    unfold stockCaseRecordAddress
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  change (stockCaseRecordAddress index + 8#64).toNat = _ ∧
    (stockCaseRecordAddress index + 8#64).toNat + 8 = _
  rw [(stockCaseArgumentSpan index).2.2.2, address]
  exact ⟨rfl, rfl⟩

theorem stockCaseLengthReadEffects (e : Executable) (code : StockCaseSelectionAt e) (s : MachineData)
    (index : Fin stockCaseArguments.length)
    (r12 : s.regs.r12.toBitVec = stockCaseRecordAddress index)
    (read : s.dmem.loadInt (stockCaseRecordAddress index + 8#64) 8 =
      some (stockCaseLength index).toBitVec.unsigned) :
    e.step ⟨s, 0x4003cc⟩ .done =
      .require_exec_access ⟨0x4003cc, 0x4003d1⟩ (fun () =>
        .require_read_access (stockCaseLengthReadSpan index) (fun () =>
          .done ⟨{ s with regs := { s.regs with rdx := stockCaseLength index } }, 0x4003d1⟩)) := by
  unfold Executable.step
  rw [code.length]
  simp only [selectCaseLength, Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    Operand.interp, RegOrMem.interp, AddrExpr.interp, ConstExpr.interp, MachineData.load]
  simp only [Width.bits, Width.bytes, Reg64s.get64, BitVec.toAddressSize, AddressSize.address_size,
    BitVec.signed, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq, Int.add_zero]
  have eight : (8 : Int64).toInt = 8 := by decide
  have offset : BitVec.ofInt 64 8 = 8#64 := by decide
  rw [eight, BitVec.ofInt_add, BitVec.ofInt_toInt, r12, offset]
  simp only [BitVec.take, BitVec.extractLsb'_eq_self]
  rw [read]
  have decode : BitVec.ofInt 64 (stockCaseLength index).toBitVec.unsigned =
      (stockCaseLength index).toBitVec := by
    rw [BitVec.unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [decode]
  have noWrap : ((stockCaseRecordAddress index + 8#64).toFin.castSucc : AddressBound).val +
      (UInt64.ofNat 8).toNat ≤ UInt64.size := by
    change (stockCaseRecordAddress index + 8#64).toNat + 8 ≤ 2 ^ 64
    rw [(stockCaseArgumentSpan index).2.2.2]
    have bound := (stockCaseArgumentSpan index).2.1
    omega
  simp only [require_access, dite_eq_left noWrap]
  rfl

def selectedCaseAddData (s : MachineData) : MachineData :=
  afterSelectCaseAdd (afterSelectCaseShift (afterSelectCaseLea s) false false)

def stockCaseSelectionSuccessor (s : MachineData) (index : Fin stockCaseArguments.length) : MachineState :=
  let selected := selectedCaseAddData s
  ⟨{ s with
      regs := { s.regs with
        rbx := selected.regs.rbx
        r12 := selected.regs.r12
        rdx := stockCaseLength index }
      status := selected.status }, 0x4003d1⟩

theorem selectedCaseR12 (s : MachineData) (index : Fin stockCaseArguments.length)
    (selector : s.regs.rbx.toBitVec = BitVec.ofNat 64 index.val) :
    (selectedCaseAddData s).regs.r12.toBitVec = stockCaseRecordAddress index := by
  change (s.regs.rbx.toBitVec <<< (5 : Nat)) + 0x403000#64 = stockCaseRecordAddress index
  rw [selector]
  have address : ∀ i : Fin stockCaseArguments.length,
      (BitVec.ofNat 64 i.val <<< (5 : Nat)) + 0x403000#64 = stockCaseRecordAddress i := by
    decide
  exact address index

private theorem selectAdvance {e : Executable} {post : MachineState → Prop} {s t : MachineState}
    (step : step1 e s (· = t)) (next : Eventually (step1 e) post t) :
    Eventually (step1 e) post s :=
  .step s (· = t) step (fun _ eq => eq ▸ next)

theorem stockCaseSelectionEventually (e : Executable) (code : StockCaseSelectionAt e)
    (file : List UInt8) (s : MachineData) (index : Fin stockCaseArguments.length)
    (selector : s.regs.rbx.toBitVec = BitVec.ofNat 64 index.val)
    (fileSlice : stockCaseFileArguments file index = stockCaseArgumentBytes index)
    (mapped : StockCaseArgumentsMapped file s.dmem index) (post : MachineState → Prop)
    (continueFrom : Eventually (step1 e) post (stockCaseSelectionSuccessor s index)) :
    Eventually (step1 e) post ⟨s, 0x4003be⟩ := by
  let afterLea := afterSelectCaseLea s
  apply selectAdvance (t := ⟨afterLea, 0x4003c5⟩)
  · exact (selectCaseLeaStep e code s _).mpr rfl
  apply Eventually.step _ (fun t => ∃ af of, t = ⟨afterSelectCaseShift afterLea af of, 0x4003c9⟩)
  · unfold step1
    rw [selectCaseShiftEffects e code afterLea]
    intro af of
    exact ⟨af, of, rfl⟩
  intro shifted h
  obtain ⟨af, of, rfl⟩ := h
  let selected := selectedCaseAddData s
  apply selectAdvance (t := ⟨selected, 0x4003cc⟩)
  · exact (selectCaseAddStep e code (afterSelectCaseShift afterLea af of) _).mpr rfl
  have length := (stockCaseLoadsOfMappedFile file s.dmem index fileSlice mapped).2
  have readStep := stockCaseLengthReadEffects e code selected index (selectedCaseR12 s index selector) length
  apply selectAdvance (t := stockCaseSelectionSuccessor s index)
  · unfold step1
    rw [readStep]
    rfl
  · exact continueFrom

#print axioms stockCaseLengthReadSpanBounds
#print axioms stockCaseLengthReadEffects
#print axioms selectedCaseR12
#print axioms stockCaseSelectionEventually

end LeanVM.Admission
