import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem satfil_wt {τ : Type} (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    Finsupp.weight wt ν = (Finsupp.weight (posW wt) ν : ℤ) - (Finsupp.weight (negW wt) ν : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [posW, negW, nsmul_eq_mul, smul_eq_mul]
  push_cast
  rw [← mul_sub, Int.toNat_sub_toNat_neg]

private theorem satfil_deg {τ : Type} (wt : τ → ℤ) (h : ∀ i, wt i ≠ 0) (ν : τ →₀ ℕ) :
    Finsupp.degree ν ≤ Finsupp.weight (posW wt) ν + Finsupp.weight (negW wt) ν := by
  change (∑ i ∈ ν.support, ν i) ≤ _
  simp only [Finsupp.weight_apply, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi : 1 ≤ posW wt i + negW wt i := by
    simp only [posW, negW]
    have := h i
    omega
  simp only [smul_eq_mul]
  nlinarith

theorem UpperTheory.V.Alg.M.satfil_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
      (∀ f ∈ 𝒜 (-1), f ∈ satSq x → φ f ∈ fil (FractionRing O) wt 2) ∧ ∀ b ∈ 𝒜 0, x b = 0 → φ b ∈ fil (FractionRing O) wt 1 := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx τ _ wt φ hφ
  have hnz : ∀ i, wt i ≠ 0 := by
    intro i
    rcases hφ.wts i with h | h | h | h <;> omega
  have hlow : ∀ y ∈ RingHom.ker x ^ 2, ∀ ν : τ →₀ ℕ, Finsupp.degree ν ≤ 1 →
      MvPowerSeries.coeff ν (φ y) = 0 := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm n hn ν hν
      classical
      rw [map_mul, MvPowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hd : Finsupp.degree p.1 + Finsupp.degree p.2 ≤ 1 := by
        rw [← map_add, hp]
        exact hν
      have hm0 : MvPowerSeries.coeff 0 (φ m) = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, RingHom.mem_ker.mp hm, map_zero]
      have hn0 : MvPowerSeries.coeff 0 (φ n) = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, RingHom.mem_ker.mp hn, map_zero]
      by_cases h1 : Finsupp.degree p.1 = 0
      · rw [(Finsupp.degree_eq_zero_iff _).mp h1, hm0, zero_mul]
      · have h2 : Finsupp.degree p.2 = 0 := by omega
        rw [(Finsupp.degree_eq_zero_iff _).mp h2, hn0, mul_zero]
    · intro a b ha hb ν hν
      rw [map_add, map_add, ha ν hν, hb ν hν, add_zero]
  refine ⟨?_, ?_⟩
  · intro f hf hsat ν hν
    obtain ⟨c, hc, hcf⟩ := hsat
    by_contra hne
    have hw : Finsupp.weight wt ν = -1 := by
      by_contra h'
      exact hne (hφ.graded (-1) f hf ν h')
    have e := satfil_wt wt ν
    have hdeg := satfil_deg wt hnz ν
    have hd1 : Finsupp.degree ν ≤ 1 := by omega
    have h0 := hlow _ hcf ν hd1
    rw [map_smul, ← algebraMap_smul (FractionRing O) c (φ f), map_smul, smul_eq_mul] at h0
    have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
      intro hz
      exact hc (IsFractionRing.injective O (FractionRing O) (by rw [hz, map_zero]))
    exact hne ((mul_eq_zero.mp h0).resolve_left hc')
  · intro b hb hxb ν hν
    by_contra hne
    have hw : Finsupp.weight wt ν = 0 := by
      by_contra h'
      exact hne (hφ.graded 0 b hb ν h')
    have e := satfil_wt wt ν
    have hdeg := satfil_deg wt hnz ν
    have hd : Finsupp.degree ν = 0 := by omega
    rw [(Finsupp.degree_eq_zero_iff _).mp hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, hxb,
      map_zero] at hne
    exact hne rfl
