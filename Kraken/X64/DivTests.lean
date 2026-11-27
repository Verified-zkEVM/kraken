module

import Kraken.X64.Parser
meta import Kraken.X64.Parser
import Kraken.X64.PrintATT
meta import Kraken.X64.PrintATT
import Kraken.X64.PrintIntel
meta import Kraken.X64.PrintIntel
import Kraken.X64.ProcSpec

private def div32 : Instr := .regular .W64 .W32 (.div (.low .rsi .W32))
private def div64 : Instr := .regular .W64 .W64 (.div (.low .rsi .W64))

example : ⸨prog| divl %esi ⸩ = [.instr div32] := rfl
example : ⸨prog| divq %rsi ⸩ = [.instr div64] := rfl
example : ⸨prog| div %esi ⸩ = [.instr div32] := rfl
example : ⸨prog| div %rsi ⸩ = [.instr div64] := rfl

private abbrev Word32 : Width := .W32

example (r : Reg Word32) : ⸨instr| div %❰r❱ ⸩ = ⸨instr| divl %❰r❱ ⸩ := rfl

/-- info: fun r => ⸨instr| divl %❰r❱ ⸩ : Reg Word32 → Instr -/
#guard_msgs in
#check fun (r : Reg Word32) => Instr.regular .W64 Word32 (.div r)

/-- info: Instr.regular Width.W64 Width.W16 (Operation.div (⸨reg| %ax ⸩)) : Instr -/
#guard_msgs in
#check Instr.regular .W64 .W16 (.div (.low .rax .W16))

/-- info: fun w r => Instr.regular Width.W64 w (Operation.div r) : (w : Width) → Reg w → Instr -/
#guard_msgs in
#check fun (w : Width) (r : Reg w) => Instr.regular .W64 w (.div r)

/-- error: DIV requires a 32- or 64-bit register -/
#guard_msgs in
#check ⸨prog| div %ax ⸩

/-- error: type error: w64 != w32 -/
#guard_msgs in
#check ⸨prog| divq %esi ⸩

#guard Kraken.X64.ATT.instr div32 == "divl %esi"
#guard Kraken.X64.ATT.instr div64 == "divq %rsi"
#guard toString div32 == "div esi"
#guard toString div64 == "div rsi"

private def singleInstr (instr : Instr) (size : Nat) : Executable :=
  ⟨0x400000, [⟨.instr instr, size⟩]⟩

private theorem singleInstr_step (instr : Instr) (size : Nat) (s : MachineData) :
    (singleInstr instr size).step ⟨s, 0x400000⟩ .done =
      instr.interp s ⟨0x400000, 0x400000 + .ofNat size⟩
        (fun next => .done ⟨next, 0x400000 + .ofNat size⟩)
        (fun pc next => .done ⟨next, pc⟩) := by
  simp [singleInstr, Executable.step, Kraken.Executable.directivesAtAddress,
    Kraken.Executable.withAddresses.eq_1, Kraken.Executable.withAddresses.eq_2,
    List.takeWhile, Directives.interp, Directive.interp]

private def divide32 : Executable := singleInstr div32 2
private def divide64 : Executable := singleInstr div64 3

private def input : MachineData :=
  { regs := { rax := 0x1111111100000001, rdx := 0x2222222200000001, rsi := 0x3333333300000002 }
    status := .mk true false true false true false
    df := true
    dmem := (List.replicate 16 0x42).At 0x500000 }

example (post : MachineState → Prop) :
    step1 divide32 ⟨input, 0x400000⟩ post ↔
      ∀ flags : StatusFlags,
        post ⟨{ input with regs := { input.regs with rax := 0x80000000, rdx := 1 },
                           status := flags }, 0x400002⟩ := by
  simp only [step1, divide32, singleInstr_step]
  rfl

private def sortInput : MachineData :=
  { input with regs := { input.regs with rax := 0x4000000000000000, rdx := 0, rsi := 94 } }

example (post : MachineState → Prop) :
    step1 divide64 ⟨sortInput, 0x400000⟩ post ↔
      ∀ flags : StatusFlags,
        post ⟨{ sortInput with regs := { sortInput.regs with rax := 0xae4c415c9882b9, rdx := 0x12 },
                               status := flags }, 0x400003⟩ := by
  simp only [step1, divide64, singleInstr_step]
  rfl

private def eaxDivisor : Executable :=
  singleInstr (.regular .W64 .W32 (.div (.low .rax .W32))) 2

private def eaxInput : MachineData :=
  { input with regs := { input.regs with rax := 0x1111111100000003 } }

example (post : MachineState → Prop) :
    step1 eaxDivisor ⟨eaxInput, 0x400000⟩ post ↔
      ∀ flags : StatusFlags,
        post ⟨{ eaxInput with regs := { eaxInput.regs with rax := 0x55555556, rdx := 1 },
                              status := flags }, 0x400002⟩ := by
  simp only [step1, eaxDivisor, singleInstr_step]
  rfl

private def zeroInput : MachineData :=
  { input with regs := { input.regs with rsi := 0x3333333300000000 } }

private def overflowInput : MachineData :=
  { sortInput with regs := { sortInput.regs with rdx := 1, rsi := 1 } }

private def faultAt (exe : Executable) (s : MachineData) : Effects :=
  match exe.step ⟨s, 0x400000⟩ .done with
  | .require_exec_access _ next => next ()
  | effect => effect

example : faultAt divide32 zeroInput = .divide_error ⟨zeroInput, 0x400000⟩ := by
  simp only [faultAt, divide32, singleInstr_step]
  rfl
example : faultAt divide64 overflowInput = .divide_error ⟨overflowInput, 0x400000⟩ := by
  simp only [faultAt, divide64, singleInstr_step]
  rfl

example : ¬ divide32.ProcSpec 0x400000 0x400002 (· = zeroInput) (fun _ _ => True) := by
  intro proc
  have run := proc zeroInput rfl
  cases run with
  | done _ atReturn => exact (by decide : (0x400000 : Int64) ≠ 0x400002) atReturn.1
  | step _ _ fault _ =>
    simp only [step1, divide32, singleInstr_step] at fault
    exact fault
