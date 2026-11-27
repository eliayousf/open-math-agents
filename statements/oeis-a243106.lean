import Mathlib

/-!
# Cano's digit conjecture for A243106

Source: https://oeis.org/A243106.
A finite list of signs encodes the coefficients at powers b^1 through
b^n, where n is the list length. The zero at the front omits the
constant term. The conjecture says that each digit of the absolute
value is 0, 1, b−2, or b−1 for every base b ≥ 5.
-/

namespace OMA.S_oeis_a243106

def digitValue (b : ℕ) : List ℤ → ℤ
  | [] => 0
  | c :: cs => c + (b : ℤ)*digitValue b cs

def AllowedDigit (b d : ℕ) : Prop := d=0 ∨ d=1 ∨ d=b-2 ∨ d=b-1

theorem main : ∀ b : ℕ, 5 ≤ b → ∀ signs : List ℤ,
    (∀ c ∈ signs, c = -1 ∨ c = 1) →
    ∀ d ∈ Nat.digits b ((digitValue b (0 :: signs)).natAbs), AllowedDigit b d := by
  sorry

end OMA.S_oeis_a243106
