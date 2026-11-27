import Mathlib.RingTheory.PowerSeries.Basic

/-! Mathar's original recurrence and denominator-cleared generating function for
strict third-order maximal independent sets in paths.

The published decomposition uses A001687(n+6) minus the parity-dependent maximum counts.
The initial index follows the source offset and the degree of its numerator.
Source: https://oeis.org/A007384/internal
-/

open PowerSeries

namespace OMA.S_oeis_a007384

def total : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 3
  | n + 5 => total (n + 3) + total n

def excluded (n : ℕ) : ℤ := if n % 2 = 0 then (n / 2 : ℕ) + 1 else 1

def a (n : ℕ) : ℤ := total n - excluded n

theorem main :
    (∀ n : ℕ, 10 ≤ n →
      a n = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 5) + a (n - 6) -
        2 * a (n - 7) + a (n - 9)) ∧
    (((1 - X ^ 2 - X ^ 5) * (1 - X ^ 2) ^ 2 : ℤ⟦X⟧) * mk a = X ^ 5) := by
  sorry

end OMA.S_oeis_a007384
