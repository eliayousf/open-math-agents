import Mathlib

/-!
# The recurrence for the original nonalternating A022030 rule

Source: https://oeis.org/A022030.
Hasler conjectured a generating function for the sequence b from
the original rule, which always takes the greatest integer giving
a strictly smaller ratio. The first two terms are 4 and 16.
For positive consecutive terms p and q, that greatest integer
is the floor of (q²−1)/p. The conjectured generating function has
initial third term 63 and recurrence b(n+3)=4b(n+2)−b(n).
-/

namespace OMA.S_oeis_a022030

def b : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | n + 2 => (b (n+1)^2-1) / b n

theorem main : b 2 = 63 ∧ ∀ n : ℕ, b (n+3) = 4*b (n+2)-b n := by
  sorry

end OMA.S_oeis_a022030
