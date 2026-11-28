import AdmissionImage

namespace LeanVM.Admission

private def fragmentGap (size : Nat) : Kraken.Sized Directive :=
  ⟨.byteArray ⟨Array.replicate size 0⟩, size⟩

private def stockAdmissionFragment : Executable :=
  ⟨0x4003d1, stockAdmissionPlan.map (·.instruction) ++
    [fragmentGap (0x4004fa - 0x400449), ⟨.label "reject_input", 0⟩,
     fragmentGap (0x400501 - 0x4004fa), ⟨.label "reject_range", 0⟩]⟩

def stockAdmissionFragmentOfSlice (slice : List UInt8) : Option Executable :=
  if slice = stockAdmissionBytes then some stockAdmissionFragment else none

private theorem planDirectives :
    stockAdmissionPlan.map (·.instruction) = stockAdmissionCode.map Prod.snd := by rfl

private theorem fragmentDirectiveAt (row : StockAdmissionRow) (member : row ∈ stockAdmissionPlan) :
    stockAdmissionFragment.directivesAtAddress row.pc = [row.instruction] := by
  have inCode : (row.pc, row.instruction) ∈ stockAdmissionCode := by
    rw [← stockAdmissionPlanCode]
    exact List.mem_map_of_mem member
  generalize row.pc = pc at *
  generalize row.instruction = instr at *
  simp only [stockAdmissionCode, callSetupCode, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at inCode
  rcases inCode with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
    simp [Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses,
      stockAdmissionFragment, planDirectives, stockAdmissionCode, rangeCmp, rangeJae, tableLea,
      tableCmp, budgetJa, callSetupCode]

private theorem fragmentRangeLabel :
    stockAdmissionFragment.labels.label? "reject_range" = some 0x400501 := by
  change stockAdmissionFragment.withAddresses.findSome? (fun d =>
    if d.directive = .label "reject_range" then some d.addr else none) = some 0x400501
  simp [Kraken.Executable.withAddresses, stockAdmissionFragment, planDirectives, stockAdmissionCode,
    rangeCmp, rangeJae, tableLea, tableCmp, budgetJa, callSetupCode, fragmentGap]

private theorem fragmentBudgetLabel :
    stockAdmissionFragment.labels.label? "reject_input" = some 0x4004fa := by
  change stockAdmissionFragment.withAddresses.findSome? (fun d =>
    if d.directive = .label "reject_input" then some d.addr else none) = some 0x4004fa
  simp [Kraken.Executable.withAddresses, stockAdmissionFragment, planDirectives, stockAdmissionCode,
    rangeCmp, rangeJae, tableLea, tableCmp, budgetJa, callSetupCode, fragmentGap]

theorem stockAdmissionFragmentPlacement (file : List UInt8) {e : Executable}
    (accepted : stockAdmissionFragmentOfSlice ((file.drop 0x3d1).take 120) = some e) :
    StockAdmissionPlacement e (readStockAdmissionFile file) := by
  unfold stockAdmissionFragmentOfSlice at accepted
  split at accepted
  · rename_i slice
    have h := Option.some.inj accepted
    subst e
    exact stockAdmissionPlacementOfFile _ file slice fragmentDirectiveAt fragmentRangeLabel fragmentBudgetLabel
  · contradiction

set_option maxRecDepth 4096 in
example : (stockAdmissionFragmentOfSlice stockAdmissionBytes).isSome = true := by decide +kernel

set_option maxRecDepth 4096 in
example : (stockAdmissionFragmentOfSlice (stockAdmissionBytes.take 119)).isNone = true := by
  decide +kernel

example : (stockAdmissionFragmentOfSlice (0 :: stockAdmissionBytes.drop 1)).isNone = true := by
  decide +kernel

#print axioms stockAdmissionFragmentPlacement

end LeanVM.Admission
