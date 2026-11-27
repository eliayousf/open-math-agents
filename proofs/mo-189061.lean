import OMAStatements.S_mo_189061
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Polynomial OMA.S_mo_189061

namespace HurwitzCounterexample

private noncomputable def stable : Polynomial ℝ :=
  (X + C 35) * (X + C 43) * (X + C 45) * (C 601 * X ^ 2 + C 2 * X + C 6746688)

private theorem noRightRoot : ¬ hasRightRoot stable := by
  rintro ⟨z, hz, hroot⟩
  have hprod : (z + 35) * (z + 43) * (z + 45) *
      (601 * z ^ 2 + 2 * z + 6746688) = 0 := by
    simpa [stable] using hroot
  rcases mul_eq_zero.mp hprod with hlin | hquad
  · rcases mul_eq_zero.mp hlin with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · have h := congrArg Complex.re h1
        norm_num [Complex.add_re] at h
        linarith
      · have h := congrArg Complex.re h2
        norm_num [Complex.add_re] at h
        linarith
    · have h := congrArg Complex.re h3
      norm_num [Complex.add_re] at h
      linarith
  · have him := congrArg Complex.im hquad
    norm_num [pow_two, Complex.add_im, Complex.mul_im, Complex.mul_re] at him
    have heq : (1202 * z.re + 2) * z.im = 0 := by linarith
    have hpos : 0 < 1202 * z.re + 2 := by linarith
    have hy : z.im = 0 := (mul_eq_zero.mp heq).resolve_left hpos.ne'
    have hre := congrArg Complex.re hquad
    norm_num [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, hy] at hre
    nlinarith [sq_nonneg z.re]

theorem counterexample : ¬ (type_of% @OMA.S_mo_189061.main) := by
  intro h
  let p := stable - C (stable.eval 0)
  have hp : p.eval 0 = 0 := by simp [p]
  have hpRoot : hasRightRoot p := by
    refine ⟨⟨1, 108⟩, by norm_num, ?_⟩
    apply Complex.ext <;>
      norm_num [p, stable, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.sub_re, Complex.sub_im]
  have hperturb := h p hp hpRoot (stable.eval 0)
  have heq : p + C (stable.eval 0) = stable := by exact sub_add_cancel _ _
  rw [heq] at hperturb
  exact noRightRoot hperturb

end HurwitzCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_189061.main) := HurwitzCounterexample.counterexample
