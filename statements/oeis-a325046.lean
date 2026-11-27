import Mathlib

/-!
# The odd coefficients of A325046

Source: https://oeis.org/A325046.
The conjecture says that an odd coefficient can occur only at index
k(k+1). We use the equivalent generating function written as the sum
over n and k of x^n choose(n,k) (x^n+x^k)^(n-k).

With j of the n-k factors contributing x^n, the exponent is
n+n*j+k*(n-k-j). Its coefficient is choose(n,k) choose(n-k,j).
Equivalently, in the original generating function use outer
index n-k, index j for the numerator, and index k for the
negative-binomial expansion. This gives the same exponent and
coefficient. All three indices are at most the target degree.
-/

namespace OMA.S_oeis_a325046

def indices (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (N+1)) ×ˢ ((Finset.range (N+1)) ×ˢ (Finset.range (N+1)))).filter
    fun (n,k,j) => k+j ≤ n ∧ N = n+n*j+k*(n-k-j)

def weight (t : ℕ × ℕ × ℕ) : ℕ :=
  t.1.choose t.2.1 * (t.1-t.2.1).choose t.2.2

def a (N : ℕ) : ℕ := ∑ t ∈ indices N, weight t

theorem main : ∀ N : ℕ, Odd (a N) → ∃ k : ℕ, N = k*(k+1) := by
  sorry

end OMA.S_oeis_a325046
