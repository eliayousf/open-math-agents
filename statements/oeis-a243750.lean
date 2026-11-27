import Mathlib

/-!
# The conjectured record indices of A243750

Sources: https://oeis.org/A243750 and https://oeis.org/A112801.
A112801 counts partitions of 2n-1 into three ordered-by-size parts
x ≤ y ≤ z, each having exactly two distinct prime factors. Exponents
in a part's factorization may exceed one. At index n the outer loop
takes x ≤ (2n-1)/3, and the inner loop takes x ≤ y ≤ (2n-1-x)/2.
The third part is then fixed. The array stores the factor test for
every possible part of that partition.

The conjecture predicts that, above 103, the strict record indices
of this count are exactly the indices congruent to 2 modulo 3.
-/

namespace OMA.S_oeis_a243750

def count (n : ℕ) : ℕ :=
  let total := 2*n-1
  let good : Array Bool := Array.ofFn fun k : Fin (total+1) =>
    decide (k.val.primeFactors.card = 2)
  let firsts := (List.range (total/3+1)).filter fun x => good[x]!
  (firsts.map fun x =>
    (List.range' x ((total-x)/2+1-x)).countP fun y =>
      good[y]! && good[total-x-y]!).sum

def IsRecord (n : ℕ) : Prop := ∀ m : ℕ, 0 < m → m < n → count m < count n

theorem main : ∀ n : ℕ, 103 < n → (IsRecord n ↔ n % 3 = 2) := by
  sorry

end OMA.S_oeis_a243750
