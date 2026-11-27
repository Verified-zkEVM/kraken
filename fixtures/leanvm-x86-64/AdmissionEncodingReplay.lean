import AdmissionImage
import Kraken.X64.PrintATT

namespace LeanVM.Admission

private def rowStart (index : Nat) : String := s!".Lrow_{index}"
private def rowEnd (index : Nat) : String := s!".Lafter_{index}"
private def sectionOffset (pc : Int64) : Nat := pc.toBitVec.toNat - 0x400000

private def renderRow (row : StockAdmissionRow) (index : Nat) : IO (String × List String) := do
  let printed := Kraken.X64.ATT.directive row.instruction.directive
  if printed.startsWith "cmpq $" then
    match (printed.drop 6).toString.splitOn ", " with
    | [immediate, destination] =>
      let symbol := s!".Lcmp_{index}"
      return (s!"cmpq ${symbol}, {destination}", [s!".set {symbol}, {immediate}"])
    | _ => throw (IO.userError s!"Unexpected printed CMP instruction: {printed}")
  if printed.startsWith "call " then
    return (s!"call {rowEnd index}+({(printed.drop 5).toString})", [])
  return (printed, [])

private def branchSymbols : IO (List (Nat × String)) := do
  let some (_, rangeTarget) :=
    decodeStockRel32 stockAdmissionRows[1].1 stockAdmissionRows[1].2
    | throw (IO.userError "Could not decode the stock range branch")
  let some (_, budgetTarget) :=
    decodeStockRel32 stockAdmissionRows[4].1 stockAdmissionRows[4].2
    | throw (IO.userError "Could not decode the stock budget branch")
  return [(sectionOffset budgetTarget, "reject_input"), (sectionOffset rangeTarget, "reject_range")]

private def renderAssembly (rows : List StockAdmissionRow) (targets : List (Nat × String)) :
    IO String := do
  let mut lines := [".text", ".org 0x3d1"]
  let mut equates := []
  for (row, index) in rows.zipIdx do
    let (asm, trailing) ← renderRow row index
    lines := lines ++ [s!"{rowStart index}:", asm, s!"{rowEnd index}:"]
    equates := equates ++ trailing
  let labels := targets.flatMap fun (offset, name) => [s!".org {offset}", s!"{name}:"]
  return "\n".intercalate (lines ++ equates ++ labels) ++ "\n"

private def runTool (directory : System.FilePath) (cmd : String) (args : Array String) :
    IO String := do
  let result ← IO.Process.output { cmd, args, cwd := some directory, env := #[("LC_ALL", some "C")] }
  unless result.exitCode == 0 do
    throw (IO.userError s!"{cmd} exited {result.exitCode}\n{result.stderr}")
  return result.stdout

private def symbolOffset (symbols : String) (name : String) : IO Nat := do
  for line in symbols.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | symbol :: _ :: value :: _ =>
      if symbol == name then
        let some offset := value.toNat? | throw (IO.userError s!"Invalid offset for {name}")
        return offset
    | _ => pure ()
  throw (IO.userError s!"Missing assembly symbol {name}")

private def assembleRows (directory : System.FilePath) (rows : List StockAdmissionRow) :
    IO (List UInt8) := do
  let targets ← branchSymbols
  IO.FS.writeFile (directory / "admission.s") (← renderAssembly rows targets)
  let _ ← runTool directory "as" #["--64", "--keep-locals", "--fatal-warnings", "-o",
    "admission.o", "admission.s"]
  let relocations ← runTool directory "readelf" #["-rW", "admission.o"]
  unless relocations.trimAscii.toString == "There are no relocations in this file." do
    throw (IO.userError s!"Unexpected assembly relocations\n{relocations}")
  let symbols ← runTool directory "nm" #["--format=posix", "--radix=d", "admission.o"]
  for (expectedOffset, name) in targets do
    unless (← symbolOffset symbols name) == expectedOffset do
      throw (IO.userError s!"Assembly label {name} has a different address")
  for (row, index) in rows.zipIdx do
    let start ← symbolOffset symbols (rowStart index)
    let stop ← symbolOffset symbols (rowEnd index)
    unless start == sectionOffset row.pc && stop == start + row.instruction.size do
      throw (IO.userError s!"Assembly instruction {index} has a different start or size")
  let _ ← runTool directory "objcopy" #["-O", "binary", "-j", ".text", "admission.o", "admission.bin"]
  let bytes ← IO.FS.readBinFile (directory / "admission.bin")
  return (bytes.extract 0x3d1 0x449).toList

private def withChangedRangeImmediate (rows : List StockAdmissionRow) : IO (List StockAdmissionRow) := do
  let first :: rest := rows | throw (IO.userError "Missing stock admission rows")
  let .instr (.regular aw w (.cmp destination (.imm (.int64 immediate)))) :=
    first.instruction.directive | throw (IO.userError "Expected the stock range CMP first")
  let directive := .instr (.regular aw w (.cmp destination (.imm (.int64 (immediate + 1)))))
  return { first with instruction := { first.instruction with directive } } :: rest

private def replayAdmissionEncoding : IO Unit := IO.FS.withTempDir fun directory => do
  let assembled ← assembleRows directory stockAdmissionPlan
  unless assembled == stockAdmissionBytes do
    throw (IO.userError "Assembled admission instructions differ from the stock bytes")
  let changed ← assembleRows directory (← withChangedRangeImmediate stockAdmissionPlan)
  unless changed != assembled && changed.drop rangeCmp.size == assembled.drop rangeCmp.size do
    throw (IO.userError "The changed range CMP operand must change only the first row")
  IO.println "All 16 printed instructions match the stock bytes and boundaries."
  IO.println "The changed range CMP operand differs from the stock bytes."

#eval replayAdmissionEncoding

end LeanVM.Admission
