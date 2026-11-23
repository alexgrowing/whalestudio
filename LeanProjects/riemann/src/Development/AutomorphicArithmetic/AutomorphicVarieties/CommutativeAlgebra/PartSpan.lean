import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.part_span :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R) (S : Set (W.σ →₀ ℕ)) (j : X), (∀ n ∈ S, Finsupp.weight W.wt n = j) →
      ∃ μ : Finset (W.σ →₀ ℕ), (μ : Set _) ⊆ S ∧ ∀ f : MvPowerSeries W.σ O, (∀ n, n ∉ S → coeff n f = 0) →
        ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, (∀ m, b m ∈ wtPart O W.wt 0) ∧ f = ∑ m ∈ μ, b m * monomial m 1 := by
  intro O R _ _ _ X _ _ _ W S j hS
  classical
  haveI := W.fin
  have hMfin : {m : W.σ →₀ ℕ | Minimal (· ∈ S) m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  have hex : ∀ n ∈ S, ∃ m ∈ {m : W.σ →₀ ℕ | Minimal (· ∈ S) m}, m ≤ n := by
    intro n hn
    obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hn
    exact ⟨b, hmin, hb⟩
  choose! c hcM hcle using hex
  refine ⟨hMfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact fun m hm => hm.1
  · intro f hf
    obtain ⟨b, hb⟩ : ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, ∀ m k,
        coeff k (b m) = if k + m ∈ S ∧ c (k + m) = m then coeff (k + m) f else 0 :=
      ⟨fun m k => if k + m ∈ S ∧ c (k + m) = m then coeff (k + m) f else 0, fun _ _ => rfl⟩
    refine ⟨b, ?_, ?_⟩
    · intro m k hk
      rw [hb, if_neg]
      rintro ⟨h1, h2⟩
      apply hk
      have hm : Finsupp.weight W.wt m = j := hS m (by rw [← h2]; exact (hcM _ h1).1)
      have hkm := hS _ h1
      rw [map_add, hm] at hkm
      simpa using hkm
    · ext n
      rw [map_sum, Finset.sum_congr rfl
        (g := fun m => if c n = m then (if n ∈ S then coeff n f else 0) else 0), Finset.sum_ite_eq]
      · by_cases hn : n ∈ S
        · rw [if_pos ((Set.Finite.mem_toFinset hMfin).2 (hcM n hn)), if_pos hn]
        · rw [hf n hn]
          simp
      · intro m _
        rw [MvPowerSeries.coeff_mul_monomial, mul_one]
        by_cases hmn : m ≤ n
        · rw [if_pos hmn, hb, tsub_add_cancel_of_le hmn]
          by_cases h1 : n ∈ S <;> by_cases h2 : c n = m <;> simp [h1, h2]
        · rw [if_neg hmn]
          by_cases h1 : n ∈ S
          · have h3 : c n ≠ m := fun h => hmn (h ▸ hcle n h1)
            simp [h3]
          · simp [h1]
