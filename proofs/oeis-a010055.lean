import OMAStatements.S_oeis_a010055

open OMA.S_oeis_a010055

private theorem lcmPrimePow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    lcmProper (p ^ (k + 1)) = p ^ k := by
  unfold lcmProper
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro d hd
    obtain ⟨j, hj, rfl⟩ := (Nat.mem_properDivisors_prime_pow hp (k + 1)).1 hd
    exact pow_dvd_pow p (by omega)
  · exact Finset.dvd_lcm (f := id)
      ((Nat.mem_properDivisors_prime_pow hp (k + 1)).2 ⟨k, Nat.lt_succ_self _, rfl⟩)

private theorem lcmOther {n : ℕ} (hn : 0 < n) (hnot : ¬ IsPrimePow n) :
    lcmProper n = n := by
  have hlcm : lcmProper n ∣ n :=
    Finset.lcm_dvd (f := id) fun d hd => (Nat.mem_properDivisors.1 hd).1
  have hlcm0 : lcmProper n ≠ 0 := by
    intro hz
    rw [hz, Nat.zero_dvd] at hlcm
    omega
  apply Nat.dvd_antisymm hlcm
  apply (Nat.factorization_le_iff_dvd hn.ne' hlcm0).mp
  intro p
  by_cases hzero : n.factorization p = 0
  · simp [hzero]
  have hp : p.Prime := by
    by_contra h
    exact hzero (Nat.factorization_eq_zero_of_not_prime n h)
  have hdiv : p ^ n.factorization p ∣ n :=
    (hp.pow_dvd_iff_le_factorization hn.ne').2 le_rfl
  have hneq : p ^ n.factorization p ≠ n := by
    intro he
    exact hnot ((isPrimePow_nat_iff n).2 ⟨p, n.factorization p, hp, Nat.pos_of_ne_zero hzero, he⟩)
  have hm : p ^ n.factorization p ∈ n.properDivisors :=
    Nat.mem_properDivisors.2 ⟨hdiv, lt_of_le_of_ne (Nat.le_of_dvd hn hdiv) hneq⟩
  exact (hp.pow_dvd_iff_le_factorization hlcm0).mp (Finset.dvd_lcm (f := id) hm)

theorem OMA.solution : type_of% @OMA.S_oeis_a010055.main := by
  intro n hn
  have hpos : 0 < n.totient := Nat.totient_pos.mpr (by omega)
  have hnat : a n * n.totient + lcmProper n = n := by
    by_cases h : IsPrimePow n
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 h
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      rw [a, if_pos (Or.inr h), one_mul, lcmPrimePow hp, Nat.totient_prime_pow_succ hp, pow_succ]
      have he : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
      calc
        p ^ j * (p - 1) + p ^ j = p ^ j * (p - 1 + 1) := by rw [mul_add, mul_one]
        _ = p ^ j * p := by rw [he]
    · simp [a, h, hn.ne', lcmOther (by omega : 0 < n) h]
  apply (eq_div_iff (by exact_mod_cast hpos.ne')).2
  apply eq_sub_of_add_eq
  exact_mod_cast hnat
