module

@[expose] public section

namespace X64

def unsignedDiv {width : Nat} (high low divisor : BitVec width) :
    Option (BitVec width × BitVec width) :=
  let dividend := high.toNat * 2 ^ width + low.toNat
  let quotient := dividend / divisor.toNat
  if divisor.toNat = 0 ∨ 2 ^ width ≤ quotient then
    none
  else
    some (BitVec.ofNat width quotient, BitVec.ofNat width (dividend % divisor.toNat))

theorem unsignedDiv_eq_none_iff {width : Nat} (high low divisor : BitVec width) :
    unsignedDiv high low divisor = none ↔ divisor.toNat ≤ high.toNat := by
  have quotient_fits (positive : 0 < divisor.toNat) :
      (high.toNat * 2 ^ width + low.toNat) / divisor.toNat < 2 ^ width ↔
        high.toNat < divisor.toNat := by
    rw [Nat.div_lt_iff_lt_mul positive, Nat.mul_comm (2 ^ width) divisor.toNat]
    constructor
    · intro dividend_lt
      have high_lt := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) dividend_lt
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos width)).mp high_lt
    · intro high_lt
      calc
        high.toNat * 2 ^ width + low.toNat < high.toNat * 2 ^ width + 2 ^ width :=
          Nat.add_lt_add_left low.isLt _
        _ = (high.toNat + 1) * 2 ^ width := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ divisor.toNat * 2 ^ width := Nat.mul_le_mul_right _ high_lt
  by_cases zero : divisor.toNat = 0
  · simp [unsignedDiv, zero]
  · have positive := Nat.pos_of_ne_zero zero
    simp [unsignedDiv, zero, ← Nat.not_lt, quotient_fits positive]

theorem unsignedDiv_eq_some {width : Nat} {high low divisor quotient remainder : BitVec width}
    (result : unsignedDiv high low divisor = some (quotient, remainder)) :
    quotient.toNat = (high.toNat * 2 ^ width + low.toNat) / divisor.toNat ∧
    remainder.toNat = (high.toNat * 2 ^ width + low.toNat) % divisor.toNat := by
  simp only [unsignedDiv] at result
  split at result
  · contradiction
  · rename_i no_error
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj result.symm)
    have positive : 0 < divisor.toNat :=
      Nat.pos_of_ne_zero fun zero => no_error (Or.inl zero)
    have quotient_fits : (high.toNat * 2 ^ width + low.toNat) / divisor.toNat < 2 ^ width :=
      Nat.lt_of_not_ge fun overflow => no_error (Or.inr overflow)
    have remainder_fits : (high.toNat * 2 ^ width + low.toNat) % divisor.toNat < 2 ^ width :=
      Nat.lt_trans (Nat.mod_lt _ positive) divisor.isLt
    simp [Nat.mod_eq_of_lt quotient_fits, Nat.mod_eq_of_lt remainder_fits]

end X64
