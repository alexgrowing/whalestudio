import Mathlib

theorem UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X :
    ∀ {O σ : Type} [inst : CommRing O] (s : Finset σ)
    (f : MvPowerSeries σ O),
    (∀ (n : σ →₀ ℕ), (∀ i ∈ s, (n : σ → ℕ) i = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
      f ∈ Ideal.span (Set.range MvPowerSeries.X) := by
  intro O σ inst s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  | insert a t hat ih =>
    intro f hf
    let g : MvPowerSeries σ O := fun n => if n a = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g =
        if n a = 0 then MvPowerSeries.coeff n f else 0 := fun n => rfl
    have h1 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) := by
      apply ih
      intro n hn
      rw [hg]
      split_ifs with h
      · apply hf
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have h2 : (MvPowerSeries.X a : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      rw [map_sub, hg, if_pos hm, sub_self]
    have h3 : f - g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)
    have h4 := Ideal.add_mem _ h3 h1
    rwa [sub_add_cancel] at h4
