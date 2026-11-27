import Mathlib

/-!
# Two progressions of least prime factors in OEIS A002586

Source: https://oeis.org/A002586 (OEIS Foundation, CC BY-SA 4.0).
Thomas König's February 15, 2017 conjecture states that the least prime factor
of 2^n + 1 is 257 at both indices n = 8 + 48k and n = 40 + 48k, for every
nonnegative integer k. Robert Israel recorded a proof on February 17, 2017.
-/

namespace OMA.S_oeis_a002586

def a (n : ℕ) : ℕ := (2 ^ n + 1).minFac

theorem main : ∀ k : ℕ, a (8 + 48 * k) = 257 ∧ a (40 + 48 * k) = 257 := by
  sorry

end OMA.S_oeis_a002586
