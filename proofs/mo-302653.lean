import OMAStatements.S_mo_302653

open Set Topology

namespace CompactSober

private def tail (n : ℕ) : Set (WithTop ℕ) := Ici (n : WithTop ℕ)

private theorem tail_zero : tail 0 = univ := by
  ext x
  cases x using WithTop.recTopCoe <;> simp [tail]

private theorem tail_antitone : Antitone tail := by
  intro n m h x hx
  exact (WithTop.coe_le_coe.mpr h).trans hx

private instance tailTopology : TopologicalSpace (WithTop ℕ) where
  IsOpen U := U = ∅ ∨ ∃ n, U = tail n
  isOpen_univ := Or.inr ⟨0, tail_zero.symm⟩
  isOpen_inter U V hU hV := by
    rcases hU with rfl | ⟨n, rfl⟩
    · exact Or.inl (empty_inter _)
    rcases hV with rfl | ⟨m, rfl⟩
    · exact Or.inl (inter_empty _)
    right
    refine ⟨max n m, ?_⟩
    rcases le_total n m with h | h
    · rw [max_eq_right h, inter_eq_right.mpr (tail_antitone h)]
    · rw [max_eq_left h, inter_eq_left.mpr (tail_antitone h)]
  isOpen_sUnion W hW := by
    classical
    by_cases h : ∃ n, tail n ∈ W
    · right
      refine ⟨Nat.find h, Subset.antisymm ?_ (subset_sUnion_of_mem (Nat.find_spec h))⟩
      intro x hx
      obtain ⟨U, hU, hxU⟩ := mem_sUnion.mp hx
      rcases hW U hU with rfl | ⟨n, rfl⟩
      · contradiction
      · exact tail_antitone (Nat.find_min' h hU) hxU
    · exact Or.inl (eq_empty_iff_forall_notMem.mpr (fun x hx => by
        obtain ⟨U, hU, hxU⟩ := mem_sUnion.mp hx
        rcases hW U hU with rfl | ⟨n, rfl⟩
        · contradiction
        · exact h ⟨n, hU⟩))

private theorem isOpen_tail (n : ℕ) : IsOpen (tail n) :=
  Or.inr ⟨n, rfl⟩

private theorem specializes_tail (x y : WithTop ℕ) : x ⤳ y ↔ y ≤ x := by
  rw [specializes_iff_forall_open]
  constructor
  · intro h
    cases x using WithTop.recTopCoe with
    | top => exact le_top
    | coe n =>
      by_contra! hlt
      have hy : y ∈ tail (n+1) := by
        cases y using WithTop.recTopCoe with
        | top => exact (show ((n+1 : ℕ) : WithTop ℕ) ≤ (⊤ : WithTop ℕ) from le_top)
        | coe m =>
          exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp hlt))
      have hx := h _ (isOpen_tail _) hy
      exact (Nat.not_succ_le_self n) (WithTop.coe_le_coe.mp hx)
  · intro h U hU hy
    change U = ∅ ∨ ∃ n, U = tail n at hU
    rcases hU with rfl | ⟨n, rfl⟩
    · contradiction
    · exact (show (n : WithTop ℕ) ≤ y from hy).trans h

private theorem ambient_t0 : T0Space (WithTop ℕ) := by
  apply (t0Space_iff_inseparable _).mpr
  intro x y h
  obtain ⟨hx, hy⟩ := inseparable_iff_specializes_and.mp h
  exact le_antisymm ((specializes_tail _ _).mp hy) ((specializes_tail _ _).mp hx)

private theorem ambient_sober : QuasiSober (WithTop ℕ) := by
  constructor
  intro U hir hcl
  have hO : Uᶜ = ∅ ∨ ∃ n, Uᶜ = tail n := hcl.isOpen_compl
  rcases hO with h | ⟨n, h⟩
  · refine ⟨⊤, ?_⟩
    rw [isGenericPoint_def]
    ext x
    rw [← specializes_iff_mem_closure, specializes_tail]
    simp only [le_top, true_iff]
    by_contra hnot
    have hx : x ∈ Uᶜ := hnot
    rw [h] at hx
    exact hx
  · have hU : U = Iio (n : WithTop ℕ) := by
      calc
        U = Uᶜᶜ := (compl_compl U).symm
        _ = (tail n)ᶜ := congrArg compl h
        _ = _ := compl_Ici
    cases n with
    | zero =>
      obtain ⟨x, hx⟩ := hir.1
      rw [hU] at hx
      cases x using WithTop.recTopCoe <;> simp at hx
    | succ n =>
      refine ⟨(n : WithTop ℕ), ?_⟩
      rw [isGenericPoint_def, hU]
      ext x
      rw [← specializes_iff_mem_closure, specializes_tail]
      cases x using WithTop.recTopCoe with
      | top => simp
      | coe m =>
        change ((m : WithTop ℕ) ≤ (n : WithTop ℕ)) ↔
          ((m : WithTop ℕ) < ((n + 1 : ℕ) : WithTop ℕ))
        exact WithTop.coe_le_coe.trans (Nat.lt_succ_iff.symm.trans WithTop.coe_lt_coe.symm)

private def finitePoints : Set (WithTop ℕ) := {x | x ≠ ⊤}

private def point (n : ℕ) : finitePoints := ⟨n, WithTop.coe_ne_top⟩

private theorem finite_compact : IsCompact finitePoints := by
  apply isCompact_iff_finite_subcover.mpr
  intro ι U hU hC
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hC (point 0).property)
  refine ⟨{i}, ?_⟩
  have hUi : U i = ∅ ∨ ∃ n, U i = tail n := hU i
  rcases hUi with hiE | ⟨n, hn⟩
  · rw [hiE] at hi
    exact False.elim hi
  · have hzero : n = 0 := by
      rw [hn] at hi
      exact Nat.eq_zero_of_le_zero (WithTop.coe_le_coe.mp hi)
    rw [hzero, tail_zero] at hn
    simp [hn]

private theorem finite_irreducible : IsIrreducible (univ : Set finitePoints) := by
  refine ⟨⟨point 0, trivial⟩, ?_⟩
  intro U V hU hV hnU hnV
  obtain ⟨A, hA, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨B, hB, rfl⟩ := isOpen_induced_iff.mp hV
  change A = ∅ ∨ ∃ n, A = tail n at hA
  change B = ∅ ∨ ∃ m, B = tail m at hB
  rcases hA with rfl | ⟨n, rfl⟩
  · simp at hnU
  rcases hB with rfl | ⟨m, rfl⟩
  · simp at hnV
  refine ⟨point (max n m), trivial, ?_, ?_⟩
  · exact WithTop.coe_le_coe.mpr (le_max_left _ _)
  · exact WithTop.coe_le_coe.mpr (le_max_right _ _)

private theorem finite_not_sober : ¬ QuasiSober finitePoints := by
  intro h
  obtain ⟨x, hx⟩ := h.sober finite_irreducible isClosed_univ
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp x.property
  have hs := hx.specializes (show point (n+1) ∈ (univ : Set finitePoints) from trivial)
  have hs' := IsInducing.subtypeVal.specializes_iff.mpr hs
  have hle := (specializes_tail _ _).mp hs'
  rw [← hn] at hle
  exact (Nat.not_succ_le_self n) (WithTop.coe_le_coe.mp hle)

theorem counterexample : ¬ (type_of% @OMA.S_mo_302653.main) := by
  intro h
  exact finite_not_sober (@h (WithTop ℕ) tailTopology ambient_t0 ambient_sober finitePoints finite_compact).2

end CompactSober

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_302653.main) := CompactSober.counterexample
