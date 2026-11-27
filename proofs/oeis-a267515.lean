import OMAStatements.S_oeis_a267515

open OMA.S_oeis_a267515

/-! The center digit at time 62 differs from the digit at time 55. -/
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267515.main) := by
  intro h
  have c62 : center 62 = true := by decide +kernel
  have c55 : center 55 = false := by decide +kernel
  have a62 : a 62 = 2 * a 61 + 1 := by
    change 2 * a 61 + ((center 62).toNat : ℤ) = _
    rw [c62]
    rfl
  have a55 : a 55 = 2 * a 54 := by
    change 2 * a 54 + ((center 55).toNat : ℤ) = _
    rw [c55]
    exact add_zero _
  have recurrence := h.1 62 (by decide)
  change a 62 = 2 * a 61 + a 55 - 2 * a 54 at recurrence
  rw [a62, a55] at recurrence
  omega
