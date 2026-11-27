import Mathlib

/-!
# Absolute Euler pseudoprimes and A307865

Sources: https://oeis.org/A307865 and https://oeis.org/A033181.
An absolute Euler pseudoprime is an odd composite m such that every
unit modulo m has its ((m−1)/2)-th power equal to 1 or −1.
The sequence counts residue classes b with b^n = −1 modulo 2n+1.
The conjecture that this count is zero is expressed by excluding
every residue class b when 2n+1 is an absolute Euler pseudoprime.
-/

namespace OMA.S_oeis_a307865

def AbsoluteEuler (m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ Odd m ∧
    ∀ x : ZMod m, IsUnit x → x^((m-1)/2) = 1 ∨ x^((m-1)/2) = -1

theorem main : ∀ n : ℕ, AbsoluteEuler (2*n+1) →
    ∀ b : ZMod (2*n+1), b^n ≠ -1 := by
  sorry

end OMA.S_oeis_a307865
