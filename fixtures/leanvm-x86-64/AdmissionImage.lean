import CallSetup
import Kraken.ToBytes

namespace LeanVM.Admission

def stockAdmissionRows : List (Int64 × List UInt8) :=
  [ (0x4003d1, [0x48, 0x81, 0xfa, 0x62, 0x00, 0x00, 0x00])
  , (0x4003d8, [0x0f, 0x83, 0x23, 0x01, 0x00, 0x00])
  , (0x4003de, [0x48, 0x8d, 0x05, 0x13, 0x46, 0x00, 0x00])
  , (0x4003e5, [0x48, 0x81, 0x3c, 0xd0, 0x00, 0x40, 0x00, 0x00])
  , (0x4003ed, [0x0f, 0x87, 0x07, 0x01, 0x00, 0x00])
  , (0x4003f3, [0x48, 0x8d, 0x3d, 0x0e, 0x4c, 0x00, 0x00])
  , (0x4003fa, [0x49, 0x8b, 0x34, 0x24])
  , (0x4003fe, [0x4c, 0x89, 0x25, 0x23, 0x4c, 0x00, 0x00])
  , (0x400405, [0x4c, 0x89, 0xec])
  , (0x400408, [0x48, 0xbb, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11])
  , (0x400412, [0x48, 0xbd, 0x99, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22])
  , (0x40041c, [0x49, 0xbc, 0xaa, 0x99, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33])
  , (0x400426, [0x49, 0xbd, 0xbb, 0xaa, 0x99, 0x88, 0x77, 0x66, 0x55, 0x44])
  , (0x400430, [0x49, 0xbe, 0xcc, 0xbb, 0xaa, 0x99, 0x88, 0x77, 0x66, 0x55])
  , (0x40043a, [0x49, 0xbf, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88, 0x77, 0x66])
  , (0x400444, [0xe8, 0xd7, 0xfc, 0xff, 0xff]) ]

def stockAdmissionBytes : List UInt8 := stockAdmissionRows.flatMap Prod.snd

private def readStockAdmissionSlice (bytes : List UInt8) (pc : Int64) (size : Nat) :
    Option (List UInt8) :=
  let address := pc.toBitVec.toNat
  let offset := address - 0x4003d1
  if 0x4003d1 ≤ address ∧ offset + size ≤ bytes.length then
    some ((bytes.drop offset).take size)
  else none

def readStockAdmissionFile (file : List UInt8) (pc : Int64) (size : Nat) : Option (List UInt8) :=
  readStockAdmissionSlice ((file.drop 0x3d1).take 120) pc size

def stockAdmissionCode : List (Int64 × Kraken.Sized Directive) :=
  [ (0x4003d1, rangeCmp)
  , (0x4003d8, rangeJae)
  , (0x4003de, tableLea)
  , (0x4003e5, tableCmp)
  , (0x4003ed, budgetJa) ] ++ callSetupCode

structure StockAdmissionRow where
  pc : Int64
  bytes : List UInt8
  instruction : Kraken.Sized Directive

def stockAdmissionPlan : List StockAdmissionRow :=
  stockAdmissionRows.zipWith (fun encoded modeled => ⟨encoded.1, encoded.2, modeled.2⟩)
    stockAdmissionCode

theorem stockAdmissionPlanRows :
    stockAdmissionPlan.map (fun row => (row.pc, row.bytes)) = stockAdmissionRows := by rfl

theorem stockAdmissionPlanCode :
    stockAdmissionPlan.map (fun row => (row.pc, row.instruction)) = stockAdmissionCode := by rfl

theorem stockAdmissionStartsAndSizes :
    stockAdmissionRows.map (fun (pc, bytes) => (pc, bytes.length)) =
      stockAdmissionCode.map (fun (pc, instr) => (pc, instr.size)) := by rfl

theorem stockAdmissionInstructionEnds :
    stockAdmissionRows.map (fun (pc, bytes) => pc + Int64.ofNat bytes.length) =
      stockAdmissionRows.tail.map Prod.fst ++ [0x400449] := by rfl

private def signedRel32 (a b c d : UInt8) : Int64 :=
  Int64.ofInt (BitVec.ofInt 32 (Int.ofBytes [a, b, c, d])).toInt

def decodeStockRel32 (pc : Int64) (bytes : List UInt8) :
    Option (Kraken.Sized Directive × Int64) :=
  match bytes with
  | [0x0f, 0x83, a, b, c, d] => some (rangeJae, pc + 6 + signedRel32 a b c d)
  | [0x0f, 0x87, a, b, c, d] => some (budgetJa, pc + 6 + signedRel32 a b c d)
  | [0xe8, a, b, c, d] =>
    let displacement := signedRel32 a b c d
    some (⟨.instr (.regular .W64 .W64 (.call (.rel (.int64 displacement)))), 5⟩,
      pc + 5 + displacement)
  | _ => none

theorem stockRangeRel32 :
    decodeStockRel32 stockAdmissionRows[1].1 stockAdmissionRows[1].2 =
      some (rangeJae, 0x400501) := by rfl

theorem stockBudgetRel32 :
    decodeStockRel32 stockAdmissionRows[4].1 stockAdmissionRows[4].2 =
      some (budgetJa, 0x4004fa) := by rfl

theorem stockCallRel32 :
    decodeStockRel32 stockAdmissionRows[15].1 stockAdmissionRows[15].2 =
      some (callSetupCode[10].2, 0x400120) := by rfl

structure StockAdmissionPlacement (e : Executable)
    (readCode : Int64 → Nat → Option (List UInt8)) : Prop where
  bytesAt : ∀ row ∈ stockAdmissionPlan, readCode row.pc row.bytes.length = some row.bytes
  directiveAt : ∀ row ∈ stockAdmissionPlan, e.directivesAtAddress row.pc = [row.instruction]
  rangeLabel : e.labels.label? "reject_range" =
    (decodeStockRel32 stockAdmissionRows[1].1 stockAdmissionRows[1].2).map Prod.snd
  budgetLabel : e.labels.label? "reject_input" =
    (decodeStockRel32 stockAdmissionRows[4].1 stockAdmissionRows[4].2).map Prod.snd

set_option maxRecDepth 2048 in
private theorem stockAdmissionSliceRows :
    stockAdmissionRows.all (fun (pc, bytes) =>
      readStockAdmissionSlice stockAdmissionBytes pc bytes.length == some bytes) = true := by
  decide +kernel

theorem stockAdmissionFileBytesAt (file : List UInt8)
    (fileSlice : (file.drop 0x3d1).take 120 = stockAdmissionBytes)
    (row : StockAdmissionRow) (inPlan : row ∈ stockAdmissionPlan) :
    readStockAdmissionFile file row.pc row.bytes.length = some row.bytes := by
  have inRows : (row.pc, row.bytes) ∈ stockAdmissionRows := by
    rw [← stockAdmissionPlanRows]
    exact List.mem_map_of_mem inPlan
  unfold readStockAdmissionFile
  rw [fileSlice]
  exact beq_iff_eq.mp (List.all_eq_true.mp stockAdmissionSliceRows _ inRows)

theorem stockAdmissionPlacementOfFile (e : Executable) (file : List UInt8)
    (fileSlice : (file.drop 0x3d1).take 120 = stockAdmissionBytes)
    (directiveAt : ∀ row ∈ stockAdmissionPlan, e.directivesAtAddress row.pc = [row.instruction])
    (rangeLabel : e.labels.label? "reject_range" = some 0x400501)
    (budgetLabel : e.labels.label? "reject_input" = some 0x4004fa) :
    StockAdmissionPlacement e (readStockAdmissionFile file) := by
  refine ⟨stockAdmissionFileBytesAt file fileSlice, directiveAt, ?_, ?_⟩
  · simpa only [stockRangeRel32, Option.map_some] using rangeLabel
  · simpa only [stockBudgetRel32, Option.map_some] using budgetLabel

theorem stockAdmissionCodeAt {e : Executable}
    {readCode : Int64 → Nat → Option (List UInt8)} (placement : StockAdmissionPlacement e readCode)
    (pc : Int64) (instr : Kraken.Sized Directive) (inCode : (pc, instr) ∈ stockAdmissionCode) :
    e.directivesAtAddress pc = [instr] := by
  rw [← stockAdmissionPlanCode] at inCode
  obtain ⟨row, inPlan, encoded⟩ := List.mem_map.mp inCode
  have model := placement.directiveAt row inPlan
  simp only [Prod.mk.injEq] at encoded
  simpa only [encoded.1, encoded.2] using model

theorem stockAdmissionGuardPlacements {e : Executable}
    {readCode : Int64 → Nat → Option (List UInt8)} (placement : StockAdmissionPlacement e readCode) :
    e.directivesAtAddress 0x4003d1 = [rangeCmp] ∧
    e.directivesAtAddress 0x4003d8 = [rangeJae] ∧
    e.labels.label? "reject_range" = some 0x400501 ∧
    e.directivesAtAddress 0x4003de = [tableLea] ∧
    e.directivesAtAddress 0x4003e5 = [tableCmp] ∧
    e.directivesAtAddress 0x4003ed = [budgetJa] ∧
    e.labels.label? "reject_input" = some 0x4004fa := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stockAdmissionCodeAt placement _ _ (List.getElem_mem (l := stockAdmissionCode) (n := 0) (by decide))
  · exact stockAdmissionCodeAt placement _ _ (List.getElem_mem (l := stockAdmissionCode) (n := 1) (by decide))
  · simpa only [stockRangeRel32, Option.map_some] using placement.rangeLabel
  · exact stockAdmissionCodeAt placement _ _ (List.getElem_mem (l := stockAdmissionCode) (n := 2) (by decide))
  · exact stockAdmissionCodeAt placement _ _ (List.getElem_mem (l := stockAdmissionCode) (n := 3) (by decide))
  · exact stockAdmissionCodeAt placement _ _ (List.getElem_mem (l := stockAdmissionCode) (n := 4) (by decide))
  · simpa only [stockBudgetRel32, Option.map_some] using placement.budgetLabel

theorem stockAdmissionCallSetupAt {e : Executable}
    {readCode : Int64 → Nat → Option (List UInt8)} (placement : StockAdmissionPlacement e readCode) :
    callSetupAt e := by
  intro pc instr inCode
  exact stockAdmissionCodeAt placement pc instr (List.mem_append_right _ inCode)

example : decodeStockRel32 0x4003d8 [0x0f, 0x83, 0x22, 0x01, 0x00, 0x00] =
    some (rangeJae, 0x400500) := by rfl

example : decodeStockRel32 0x4003ed [0x0f, 0x86, 0x07, 0x01, 0x00, 0x00] = none := by rfl

example : decodeStockRel32 0x400444 [0xe8, 0xd7, 0xfc, 0xff] = none := by rfl

example : decodeStockRel32 0x400444 [0xe8, 0xd8, 0xfc, 0xff, 0xff] =
    some (⟨.instr (.regular .W64 .W64 (.call (.rel (.int64 (-0x328))))), 5⟩, 0x400121) := by rfl

example : readStockAdmissionFile [] 0x4003d1 7 = none := by rfl

example (file : List UInt8) : readStockAdmissionFile file 0x4003d0 1 = none := by rfl

example (file : List UInt8) (fileSlice : (file.drop 0x3d1).take 120 = stockAdmissionBytes) :
    readStockAdmissionFile file 0x400448 2 = none := by
  unfold readStockAdmissionFile
  rw [fileSlice]
  rfl

#print axioms stockAdmissionStartsAndSizes
#print axioms stockAdmissionInstructionEnds
#print axioms stockRangeRel32
#print axioms stockBudgetRel32
#print axioms stockCallRel32
#print axioms stockAdmissionFileBytesAt
#print axioms stockAdmissionPlacementOfFile
#print axioms stockAdmissionGuardPlacements
#print axioms stockAdmissionCallSetupAt

end LeanVM.Admission
