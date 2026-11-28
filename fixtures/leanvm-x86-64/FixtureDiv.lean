import Kraken.X64.Semantics

namespace LeanVM.Fixture

open X64

private theorem divWithZeroHigh {w : Nat} (low divisor : BitVec w)
    (positive : 0 < divisor.toNat) :
    X64.unsignedDiv (0 : BitVec w) low divisor =
      some (BitVec.ofNat w (low.toNat / divisor.toNat),
            BitVec.ofNat w (low.toNat % divisor.toNat)) := by
  cases h : X64.unsignedDiv (0 : BitVec w) low divisor with
  | none =>
    have fault := (X64.unsignedDiv_eq_none_iff _ _ _).mp h
    simp at fault
    omega
  | some result =>
    obtain ⟨q, r⟩ := result
    obtain ⟨hq, hr⟩ := X64.unsignedDiv_eq_some h
    simp at hq hr
    rw [← hq, ← hr]
    simp

theorem allocatorDiv (cursor : BitVec 32) :
    X64.unsignedDiv (0 : BitVec 32) cursor (8 : BitVec 32) =
      some (BitVec.ofNat 32 (cursor.toNat / 8), BitVec.ofNat 32 (cursor.toNat % 8)) :=
  divWithZeroHigh cursor (8 : BitVec 32) (by decide)

theorem sortDiv (n : Nat) (lower : 21 ≤ n) (upper : n ≤ 96) :
    X64.unsignedDiv (0 : BitVec 64) (0x4000000000000000 : BitVec 64) (BitVec.ofNat 64 n) =
      some (BitVec.ofNat 64 (2 ^ 62 / n), BitVec.ofNat 64 (2 ^ 62 % n)) := by
  have fits : n < 2 ^ 64 := by omega
  have positive : 0 < (BitVec.ofNat 64 n).toNat := by
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] using (show 0 < n by omega)
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] using
    divWithZeroHigh (0x4000000000000000 : BitVec 64) (BitVec.ofNat 64 n) positive

theorem allocatorDivStep (s : MachineData) (span : Std.Rco Int64)
    (cursor : BitVec 32) (low : s.regs.get (.low .rax .W32) = cursor)
    (high : s.regs.get (.low .rdx .W32) = 0) (divisor : s.regs.get (.low .rsi .W32) = 8)
    (next : MachineData → Effects) (jump : Int64 → MachineData → Effects) :
    (Instr.regular .W64 .W32 (.div (.low .rsi .W32))).interp s span next jump =
      require_exec_access span (fun _ =>
        undefined fun status =>
          next { (s.setReg (.low .rax .W32) (BitVec.ofNat 32 (cursor.toNat / 8))).setReg
                     (.low .rdx .W32) (BitVec.ofNat 32 (cursor.toNat % 8)) with status }) := by
  simp only [Instr.interp, Operation.interp, low, high, divisor, allocatorDiv]
  rfl

theorem sortDivStep (s : MachineData) (span : Std.Rco Int64)
    (n : Nat) (lower : 21 ≤ n) (upper : n ≤ 96)
    (low : s.regs.get (.low .rax .W64) = 0x4000000000000000)
    (high : s.regs.get (.low .rdx .W64) = 0)
    (divisor : s.regs.get (.low .rsi .W64) = BitVec.ofNat 64 n)
    (next : MachineData → Effects) (jump : Int64 → MachineData → Effects) :
    (Instr.regular .W64 .W64 (.div (.low .rsi .W64))).interp s span next jump =
      require_exec_access span (fun _ =>
        undefined fun status =>
          next { (s.setReg (.low .rax .W64) (BitVec.ofNat 64 (2 ^ 62 / n))).setReg
                     (.low .rdx .W64) (BitVec.ofNat 64 (2 ^ 62 % n)) with status }) := by
  simp only [Instr.interp, Operation.interp, low, high, divisor, sortDiv n lower upper]
  rfl

#print axioms allocatorDivStep
#print axioms sortDivStep

end LeanVM.Fixture
