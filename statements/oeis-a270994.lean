import Mathlib

/-!
# The Sierpiński consecutiveness conjecture in A270994

Source: https://oeis.org/A270994.
An odd positive k is a Sierpiński number if k·2^m+1 is composite
for every positive m. The conjecture asserts that a(n) and
a(n)+28 are consecutive Sierpiński numbers for every n ≥ 0.
-/

namespace OMA.S_oeis_a270994

def a (n : ℕ) : ℕ := 9454129 + 11184810*n

def Sierpinski (k : ℕ) : Prop :=
  Odd k ∧ ∀ m : ℕ, 0 < m → ¬ (k*2^m+1).Prime

theorem main : ∀ n : ℕ, Sierpinski (a n) ∧ Sierpinski (a n+28) ∧
    ∀ k : ℕ, a n < k → k < a n+28 → ¬ Sierpinski k := by
  sorry

end OMA.S_oeis_a270994
