import CallSetup

namespace LeanVM.Admission

def stockCaseArguments : List (UInt64 × UInt64) :=
  [ (0x403d70, 0)
  , (0x403d80, 1)
  , (0x403d90, 1)
  , (0x403da0, 4)
  , (0x403de0, 96)
  , (0x4043e0, 97)
  , (0x4043e0, 98)
  , (0x4043e0, 0x200000000000000)
  , (0x403160, 94)
  , (0x403740, 54)
  , (0x403aa0, 45) ]

def stockCaseRecordAddress (index : Fin stockCaseArguments.length) : BitVec 64 :=
  BitVec.ofNat 64 (0x403000 + 32 * index.val)

def stockCaseRecordOffset (index : Fin stockCaseArguments.length) : Nat :=
  0x3000 + 32 * index.val

def stockCasePointer (index : Fin stockCaseArguments.length) : UInt64 :=
  stockCaseArguments[index.val].1

def stockCaseLength (index : Fin stockCaseArguments.length) : UInt64 :=
  stockCaseArguments[index.val].2

private def encodeWord (word : UInt64) : List UInt8 := Int.toBytes 8 (word.toNat : Int)

private theorem encodeWordLength (word : UInt64) : (encodeWord word).length = 8 :=
  Int.toBytes_length 8 _

private theorem decodeWord (word : UInt64) : Int.ofBytes (encodeWord word) = (word.toNat : Int) := by
  have bound := word.toNat_lt_size
  change word.toNat < 2 ^ 64 at bound
  unfold encodeWord
  rw [ofBytes_toBytes, Int.take]
  exact Int.emod_eq_of_lt (by omega) (by omega)

def stockCaseArgumentBytes (index : Fin stockCaseArguments.length) : List UInt8 :=
  encodeWord (stockCasePointer index) ++ encodeWord (stockCaseLength index)

def stockCaseFileArguments (file : List UInt8) (index : Fin stockCaseArguments.length) : List UInt8 :=
  (file.drop (stockCaseRecordOffset index)).take 16

def StockCaseArgumentsMapped (file : List UInt8) (m : Mem 64)
    (index : Fin stockCaseArguments.length) : Prop :=
  m.loadBytes (stockCaseRecordAddress index) 8 =
    some ((stockCaseFileArguments file index).take 8) ∧
  m.loadBytes (stockCaseRecordAddress index + 8#64) 8 =
    some ((stockCaseFileArguments file index).drop 8)

theorem stockCaseArgumentSpan (index : Fin stockCaseArguments.length) :
    let address := (stockCaseRecordAddress index).toNat
    0x403000 ≤ address ∧ address + 16 ≤ 0x403160 ∧
    0x3000 + (address - 0x403000) = stockCaseRecordOffset index ∧
    (stockCaseRecordAddress index + 8#64).toNat = address + 8 := by
  have bound : index.val < 11 := index.isLt
  dsimp only [stockCaseRecordAddress, stockCaseRecordOffset]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 0x403000 + 32 * index.val < 2 ^ 64 by omega)]
  rw [Nat.mod_eq_of_lt (show 0x403000 + 32 * index.val + 8 < 2 ^ 64 by omega)]
  omega

theorem stockCaseLoadsOfMappedFile (file : List UInt8) (m : Mem 64)
    (index : Fin stockCaseArguments.length)
    (fileSlice : stockCaseFileArguments file index = stockCaseArgumentBytes index)
    (mapped : StockCaseArgumentsMapped file m index) :
    m.loadInt (stockCaseRecordAddress index) 8 = some (stockCasePointer index).toBitVec.unsigned ∧
    m.loadInt (stockCaseRecordAddress index + 8#64) 8 = some (stockCaseLength index).toBitVec.unsigned := by
  obtain ⟨pointer, length⟩ := mapped
  rw [fileSlice, stockCaseArgumentBytes, List.take_left' (encodeWordLength _)] at pointer
  rw [fileSlice, stockCaseArgumentBytes, List.drop_left' (encodeWordLength _)] at length
  constructor
  · rw [Mem.loadInt, pointer, Option.map_some, decodeWord]
    rfl
  · rw [Mem.loadInt, length, Option.map_some, decodeWord]
    rfl

theorem stockCaseInputOfMappedFile (file : List UInt8) (s : MachineData)
    (index : Fin stockCaseArguments.length)
    (fileSlice : stockCaseFileArguments file index = stockCaseArgumentBytes index)
    (mapped : StockCaseArgumentsMapped file s.dmem index)
    (selected : s.regs.r12.toBitVec = stockCaseRecordAddress index) :
    s.dmem.loadInt s.regs.r12.toBitVec 8 = some (stockCasePointer index).toBitVec.unsigned := by
  rw [selected]
  exact (stockCaseLoadsOfMappedFile file s.dmem index fileSlice mapped).1

#print axioms stockCaseArgumentSpan
#print axioms stockCaseLoadsOfMappedFile
#print axioms stockCaseInputOfMappedFile

end LeanVM.Admission
