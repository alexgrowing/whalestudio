import Mathlib

theorem UpperTheory.Reformulated.B.Qf39.ev_decomp :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : Fintype σ]
    (f : MvPowerSeries σ O),
    ∃ (h : σ → MvPowerSeries σ O),
      f =
          (MvPowerSeries.C : O → MvPowerSeries σ O) ((MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f) +
            ∑ i : σ, MvPowerSeries.X i * h i ∧
        ∀ (i : σ),
          (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) (h i) =
            (MvPowerSeries.coeff fun₀ | i => (1 : ℕ) : MvPowerSeries σ O → O) f := by
  intro O σ _ _ f
  classical
  have key : ∀ m : σ →₀ ℕ, ∃ o : Option σ,
      (m ≠ 0 → ∃ j, o = some j) ∧ ∀ j, o = some j → m j ≠ 0 := by
    intro m
    by_cases hm : m = 0
    · exact ⟨none, fun h => (h hm).elim, fun j hj => by cases hj⟩
    · obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 hm
      refine ⟨some j, fun _ => ⟨j, rfl⟩, fun k hk => ?_⟩
      cases hk
      simpa using hj
  choose c hc₁ hc₂ using key
  let h : σ → MvPowerSeries σ O := fun i m =>
    if c (m + Finsupp.single i 1) = some i then
      MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hh : ∀ i m, MvPowerSeries.coeff m (h i) =
      if c (m + Finsupp.single i 1) = some i then
        MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 := fun _ _ => rfl
  have hX : ∀ i m, MvPowerSeries.coeff m (MvPowerSeries.X i * h i) =
      if c m = some i then MvPowerSeries.coeff m f else 0 := by
    intro i m
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hle : Finsupp.single i 1 ≤ m
    · rw [if_pos hle, hh, tsub_add_cancel_of_le hle]
    · rw [if_neg hle, if_neg]
      intro hi
      exact hle (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (hc₂ m i hi)))
  refine ⟨h, ?_, fun i => ?_⟩
  · ext m
    rw [map_add, map_sum, MvPowerSeries.coeff_C]
    simp only [hX]
    by_cases hm : m = 0
    · subst hm
      have : ∀ i, ¬ c 0 = some i := fun i hi => hc₂ 0 i hi rfl
      simp [this]
    · obtain ⟨j, hj⟩ := hc₁ m hm
      simp [hm, hj]
  · have hne : (Finsupp.single i 1 : σ →₀ ℕ) ≠ 0 := by simp
    obtain ⟨j, hj⟩ := hc₁ _ hne
    have hji : j = i := by
      by_contra hji
      exact hc₂ _ j hj (Finsupp.single_eq_of_ne hji)
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh, zero_add, if_pos (hji ▸ hj)]
