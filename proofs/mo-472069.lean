import OMAStatements.S_mo_472069
import Mathlib.GroupTheory.SpecificGroups.Dihedral

open DihedralGroup OMA.S_mo_472069
open scoped Pointwise

namespace SmallDoublingCounterexample

private def A : Finset (DihedralGroup 5) := {r 1, r 4, sr 0, sr 2}

private def H : Subgroup (DihedralGroup 5) where
  carrier := {x | x = 1 ∨ x = sr 1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    change x = 1 ∨ x = sr 1 at hx
    change y = 1 ∨ y = sr 1 at hy
    change x * y = 1 ∨ x * y = sr 1
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide
  inv_mem' := by
    intro x hx
    change x = 1 ∨ x = sr 1 at hx
    change x⁻¹ = 1 ∨ x⁻¹ = sr 1
    rcases hx with rfl | rfl <;> decide

private theorem right_stabilizer :
    ∀ h : DihedralGroup 5,
      (∀ x : DihedralGroup 5, x ∈ A * A → x * h ∈ A * A) ↔ h = 1 ∨ h = sr 1 := by
  decide

private theorem generates : Subgroup.closure (A : Set (DihedralGroup 5)) = ⊤ := by
  let K := Subgroup.closure (A : Set (DihedralGroup 5))
  have hr : r 1 ∈ K := Subgroup.subset_closure (by decide)
  have hs : sr 0 ∈ K := Subgroup.subset_closure (by decide)
  have rotations (i : ZMod 5) : r i ∈ K := by
    have hp := K.pow_mem hr i.val
    simpa [r_one_pow] using hp
  apply top_unique
  intro x _
  change x ∈ K
  cases x with
  | r i => exact rotations i
  | sr i =>
    have hp := K.mul_mem hs (rotations i)
    simpa using hp

private theorem not_normal : ¬ H.Normal := by
  intro hn
  have hs : sr (1 : ZMod 5) ∈ H := Or.inr rfl
  have hh := hn.conj_mem _ hs (r 1)
  change r (1 : ZMod 5) * sr 1 * (r 1)⁻¹ = 1 ∨
    r (1 : ZMod 5) * sr 1 * (r 1)⁻¹ = sr 1 at hh
  exact (by decide : ¬ (r (1 : ZMod 5) * sr 1 * (r 1)⁻¹ = 1 ∨
    r (1 : ZMod 5) * sr 1 * (r 1)⁻¹ = sr 1)) hh

theorem counterexample : ¬ (type_of% @OMA.S_mo_472069.main) := by
  intro h
  apply not_normal
  apply h (DihedralGroup 5) A H generates
  · intro x hx y hy
    exact (right_stabilizer y).mpr hy x hx
  · intro K _ hK z hz
    exact (right_stabilizer z).mp (fun x hx => hK x hx z hz)
  · decide

end SmallDoublingCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_472069.main) := SmallDoublingCounterexample.counterexample
