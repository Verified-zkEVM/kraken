import AdmissionGuards

namespace LeanVM.Admission

private def tableWord (n : Nat) : List UInt8 :=
  (littleEndian64 (stackRequired n)).toList

private theorem wordLength (n : Nat) : (tableWord n).length = 8 := by
  simp [tableWord, littleEndian64]

def stockTableBytes : List UInt8 :=
  (List.range stackTableLength).flatMap tableWord

private theorem flatMapTableByte (indices : List Nat) (n i : Nat)
    (inRange : n < indices.length) (inWord : i < 8) :
    (indices.flatMap tableWord)[8 * n + i]? = (tableWord indices[n])[i]? := by
  induction indices generalizing n with
  | nil => simp at inRange
  | cons j indices ih =>
    cases n with
    | zero => simp [List.getElem?_append, wordLength, inWord]
    | succ n =>
      have tailRange : n < indices.length := by simpa using inRange
      have selected : 8 * (n + 1) + i = 8 + (8 * n + i) := by omega
      have pastHead : ¬ 8 + (8 * n + i) < 8 := by omega
      simpa [List.getElem?_append, wordLength, selected, pastHead] using ih n tailRange

private theorem tableByte (n i : Nat)
    (inRange : n < stackTableLength) (inWord : i < 8) :
    stockTableBytes[8 * n + i]? = (tableWord n)[i]? := by
  have range : n < (List.range stackTableLength).length := by simpa using inRange
  simpa [stockTableBytes, List.getElem_range range] using
    flatMapTableByte (List.range stackTableLength) n i range inWord

private theorem wordValue :
    ∀ n : Fin stackTableLength,
      Int.ofBytes (tableWord n.val) = (stackRequired n.val : Int) := by
  decide +kernel

theorem stockTableReadFootprint (n : Nat) (inRange : n < stackTableLength) :
    let span := tableEntryReadSpan n inRange
    0x4049f8 ≤ span.lower.val ∧ span.upper.val ≤ 0x404d08 ∧
    0x403000 ≤ span.lower.val ∧ span.upper.val ≤ 0x404d30 ∧ span.upper.val ≤ 0x404d18 ∧
    0x3000 + (span.lower.val - 0x403000) = 0x49f8 + 8 * n ∧
    0x3000 + (span.upper.val - 0x403000) = 0x49f8 + 8 * n + 8 := by
  have bounds := tableEntryReadSpanBounds n inRange
  dsimp only
  rw [bounds.1, bounds.2]
  unfold stackTableLength at inRange
  omega

theorem stockTableReadPermission (n : Nat) (inRange : n < stackTableLength)
    (readable writable : Nat → Prop)
    (readOnly : ∀ address, 0x403000 ≤ address → address < 0x405000 →
      readable address ∧ ¬ writable address)
    (address : Nat)
    (aboveLower : (tableEntryReadSpan n inRange).lower.val ≤ address)
    (belowUpper : address < (tableEntryReadSpan n inRange).upper.val) :
    readable address ∧ ¬ writable address := by
  have ⟨lower, upper⟩ := tableEntryReadSpanBounds n inRange
  unfold stackTableLength at inRange
  rw [lower] at aboveLower
  rw [upper] at belowUpper
  exact readOnly address (by omega) (by omega)

private theorem loadBytesOfLookups (m : Mem 64) (addr : BitVec 64) (bs : List UInt8)
    (read : ∀ i : Nat, i < bs.length → m.get? (addr + BitVec.ofNat 64 i) = bs[i]?) :
    m.loadBytes addr bs.length = some bs := by
  have lookups : ((List.range bs.length).map fun i => m.get? (addr + BitVec.ofNat 64 i)) =
      bs.map some := by
    apply List.ext_getElem?
    intro i
    by_cases inRange : i < bs.length
    · rw [List.getElem?_map, List.getElem?_range inRange, Option.map_some, read i inRange]
      simp [List.getElem?_eq_getElem inRange]
    · have outLeft : bs.length ≤ i := Nat.le_of_not_gt inRange
      have outRange : (List.range bs.length)[i]? = none :=
        List.getElem?_eq_none (by simp [outLeft])
      rw [List.getElem?_map, outRange, List.getElem?_map, List.getElem?_eq_none outLeft]
      rfl
  rw [Mem.loadBytes, lookups]
  simpa using (List.mapM_pure (m := Option) (f := id) (l := bs))

theorem stockTableLoadOfMappedFile (file : List UInt8) (m : Mem 64)
    (fileTable : (file.drop 0x49f8).take 784 = stockTableBytes)
    (mapped : ∀ i : Nat, i < 784 →
      m.get? (BitVec.ofNat 64 (0x4049f8 + i)) = file[0x49f8 + i]?)
    (n : Nat) (inRange : n < stackTableLength) :
    m.loadInt (tableEntryAddress n) 8 = some (stackRequired n : Int) := by
  let word := tableWord n
  have wordSize : word.length = 8 := wordLength n
  have read : ∀ i : Nat, i < word.length →
      m.get? (tableEntryAddress n + BitVec.ofNat 64 i) = word[i]? := by
    intro i hi
    rw [wordSize] at hi
    have within : 8 * n + i < 784 := by
      unfold stackTableLength at inRange
      omega
    rw [tableEntryAddress, ← BitVec.ofNat_add,
      show 0x4049f8 + 8 * n + i = 0x4049f8 + (8 * n + i) by omega, mapped _ within]
    have select : ((file.drop 0x49f8).take 784)[8 * n + i]? =
        stockTableBytes[8 * n + i]? :=
      congrArg (fun (bytes : List UInt8) => bytes[8 * n + i]?) fileTable
    rw [List.getElem?_take_of_lt within, List.getElem?_drop] at select
    exact select.trans (tableByte n i inRange hi)
  have load := loadBytesOfLookups m (tableEntryAddress n) word read
  rw [wordSize] at load
  rw [Mem.loadInt, load, Option.map_some]
  exact congrArg some (wordValue ⟨n, inRange⟩)

example (file : List UInt8) (s : MachineData)
    (fileTable : (file.drop 0x49f8).take 784 = stockTableBytes)
    (mapped : ∀ i : Nat, i < 784 →
      s.dmem.get? (BitVec.ofNat 64 (0x4049f8 + i)) = file[0x49f8 + i]?) :
    s.regs.rdx.toNat < stackTableLength →
    Mem.loadInt s.dmem (tableEntryAddress s.regs.rdx.toNat) 8 =
      some (stackRequired s.regs.rdx.toNat : Int) :=
  stockTableLoadOfMappedFile file s.dmem fileTable mapped s.regs.rdx.toNat

#print axioms stockTableReadFootprint
#print axioms stockTableReadPermission
#print axioms stockTableLoadOfMappedFile

end LeanVM.Admission
