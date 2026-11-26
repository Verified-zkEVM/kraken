def stackTableLength : Nat := 98

-- Provisional entries for testing the admission path.
def stackRequired (n : Nat) : Nat := 4096 + 128 * n

def littleEndian64 (requirement : Nat) : Array UInt8 :=
  (List.range 8).toArray.map fun byte => (requirement >>> (8 * byte)).toUInt8

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "Expected an output filename")
  let mut bytes : ByteArray := ByteArray.empty
  for n in [:stackTableLength] do
    let requirement := stackRequired n
    if requirement >= 2^64 then
      throw (IO.userError s!"Unrepresentable stack requirement for length {n}")
    bytes := bytes ++ ⟨littleEndian64 requirement⟩
  IO.FS.writeBinFile path bytes
