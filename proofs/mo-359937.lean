import OMAStatements.S_mo_359937
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open OMA.S_mo_359937

namespace CubicSymmetryCounterexample

private noncomputable def matrix : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i.val = j.val then 1 / 3 else -(2 / 3)

private theorem orthogonal : matrix * matrix.transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_three]

private theorem symmetric : matrix.transpose = matrix := by
  ext i j
  simp [matrix, eq_comm]

private theorem no_blocks : ¬ HasBlockDecomposition matrix := by
  rintro ⟨S, T, ⟨i, hi⟩, hS, hST, hzeros⟩
  have hT : T.card < 3 := hST ▸ hS
  have hNotAll : ∃ j, j ∉ T := by
    by_contra! hall
    have heq : T = Finset.univ := Finset.eq_univ_of_forall hall
    simp [heq] at hT
  obtain ⟨j, hj⟩ := hNotAll
  have hz := hzeros i j (Or.inl ⟨hi, hj⟩)
  by_cases hij : i.val = j.val <;> norm_num [matrix, hij] at hz

private theorem row_identity (i j : Fin 3) :
    ∑ k, matrix i k ^ 3 * matrix j k = ∑ k, matrix j k ^ 3 * matrix i k := by
  fin_cases i <;> fin_cases j <;> norm_num [matrix, Fin.sum_univ_three]

private theorem col_identity (i j : Fin 3) :
    ∑ k, matrix k i ^ 3 * matrix k j = ∑ k, matrix k j ^ 3 * matrix k i := by
  have hs (u v : Fin 3) : matrix u v = matrix v u := by
    simpa only [Matrix.transpose_apply] using congrFun (congrFun symmetric v) u
  simpa only [hs i, hs j] using row_identity i j

theorem counterexample : ¬ (type_of% @OMA.S_mo_359937.main) := by
  intro h
  have ht : matrix.transpose * matrix = 1 := by
    simpa only [symmetric] using orthogonal
  have habs := h 3 matrix orthogonal ht no_blocks row_identity col_identity 0 0 0 1
    (by norm_num [matrix]) (by norm_num [matrix])
  norm_num [matrix] at habs

end CubicSymmetryCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_359937.main) := CubicSymmetryCounterexample.counterexample
