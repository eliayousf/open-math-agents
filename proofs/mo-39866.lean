import OMAStatements.S_mo_39866

open IsLocalRing

theorem OMA.solution : type_of% @OMA.S_mo_39866.main := by
  intro R _ _ _ h
  classical
  obtain ⟨a, ha : maximalIdeal R = Ideal.span {a}⟩ := h
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · exact ⟨⟨0, by simp [hI]⟩⟩
  have hspan (n : ℕ) : maximalIdeal R ^ n = Ideal.span {a ^ n} := by
    rw [ha, Ideal.span_singleton_pow]
  have hpow : ∃ n : ℕ, ¬ I ≤ maximalIdeal R ^ n := by
    by_contra! hAll
    apply hI
    refine le_antisymm ?_ bot_le
    rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R)
      (maximalIdeal.isMaximal R).ne_top]
    exact le_iInf hAll
  have hpos : 0 < Nat.find hpow := by
    apply Nat.pos_of_ne_zero
    intro hz
    simpa [hz, Ideal.one_eq_top] using Nat.find_spec hpow
  let k := Nat.find hpow - 1
  have hk : k + 1 = Nat.find hpow := Nat.sub_add_cancel hpos
  have hle : I ≤ maximalIdeal R ^ k := by
    by_contra hbad
    have hmin := Nat.find_min' hpow hbad
    omega
  have hnle : ¬ (I : Set R) ⊆ ((maximalIdeal R ^ (k + 1) : Ideal R) : Set R) :=
    hk.symm ▸ Nat.find_spec hpow
  obtain ⟨x, hx, hxout⟩ := Set.not_subset.mp hnle
  have hx' : x ∈ Ideal.span {a ^ k} := hspan k ▸ hle hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx'
  have hb : IsUnit b := by
    by_contra hbu
    apply hxout
    rw [pow_succ]
    apply Ideal.mul_mem_mul
    · exact hspan k ▸ Ideal.mem_span_singleton_self _
    · exact (mem_maximalIdeal b).mpr hbu
  refine ⟨⟨a ^ k, ?_⟩⟩
  change I = Ideal.span {a ^ k}
  refine le_antisymm (hspan k ▸ hle) ?_
  rw [← Ideal.span_singleton_mul_right_unit hb (a ^ k)]
  exact (Ideal.span_singleton_le_iff_mem I).mpr hx
