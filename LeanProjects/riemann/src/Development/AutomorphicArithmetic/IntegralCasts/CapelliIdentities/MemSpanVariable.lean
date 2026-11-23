import Mathlib

theorem UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X :
    ∀ {O σ : Type} [inst : CommRing O] [Fintype σ]
    (f : MvPowerSeries σ O),
    (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f = (0 : O) → f ∈ Ideal.span (Set.range MvPowerSeries.X) := by
  intro O σ _ _ f hf
  classical
  have hc : ∀ n : σ →₀ ℕ, ∃ o : Option σ, n ≠ 0 → ∃ i, o = some i ∧ n i ≠ 0 := by
    intro n
    by_cases h : n = 0
    · exact ⟨none, fun h' => absurd h h'⟩
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp h
      exact ⟨some i, fun _ => ⟨i, rfl, hi⟩⟩
  choose c hc using hc
  let g : σ → MvPowerSeries σ O := fun i m =>
    if c (m + Finsupp.single i 1) = some i then
      MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hg : ∀ i m, MvPowerSeries.coeff m (g i) =
      if c (m + Finsupp.single i 1) = some i then
        MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 := fun _ _ => rfl
  have key : ∀ (i : σ) (n : σ →₀ ℕ), MvPowerSeries.coeff n (MvPowerSeries.X i * g i) =
      if n i ≠ 0 ∧ c n = some i then MvPowerSeries.coeff n f else 0 := by
    intro i n
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
    by_cases h : n i = 0
    · have h' : ¬ Finsupp.single i 1 ≤ n := by
        rw [Finsupp.single_le_iff]; omega
      rw [if_neg h', if_neg (fun hh => hh.1 h)]
    · have h' : Finsupp.single i 1 ≤ n := by
        rw [Finsupp.single_le_iff]; omega
      rw [if_pos h', one_mul, hg, tsub_add_cancel_of_le h']
      simp [h]
  have hsum : f = ∑ i, MvPowerSeries.X i * g i := by
    ext n
    rw [map_sum]
    simp only [key]
    by_cases h : n = 0
    · subst h
      simpa using hf
    · obtain ⟨i, hi, hn⟩ := hc n h
      rw [Finset.sum_eq_single i]
      · rw [if_pos ⟨hn, hi⟩]
      · intro j _ hj
        rw [if_neg]
        rintro ⟨_, h2⟩
        exact hj (Option.some.inj (h2.symm.trans hi))
      · intro h2
        exact absurd (Finset.mem_univ i) h2
  rw [hsum]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
