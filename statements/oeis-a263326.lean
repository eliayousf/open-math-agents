import Mathlib

/-!
# Sun's conjecture on divisor reciprocal sums

Source: https://oeis.org/A263326.
For positive k and s, take the sum of 1/(d+k)^s over positive
divisors d of each positive n. The conjecture says the sums
are never integers and have pairwise distinct fractional parts.
-/

namespace OMA.S_oeis_a263326

def reciprocalSum (k s n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors, 1 / ((d : ℚ)+k)^s

def fractionalPart (x : ℚ) : ℚ := x - (⌊x⌋ : ℤ)

theorem main : ∀ k s : ℕ, 0 < k → 0 < s →
    (∀ n : ℕ, 0 < n → ¬ ∃ z : ℤ, reciprocalSum k s n = (z : ℚ)) ∧
    ∀ n m : ℕ, 0 < n → 0 < m → n ≠ m →
      fractionalPart (reciprocalSum k s n) ≠ fractionalPart (reciprocalSum k s m) := by
  sorry

end OMA.S_oeis_a263326
