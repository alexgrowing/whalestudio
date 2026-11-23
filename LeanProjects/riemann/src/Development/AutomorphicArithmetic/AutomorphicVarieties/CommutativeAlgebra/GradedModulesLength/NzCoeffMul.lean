import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem nz_coeff_mul {τ E : Type} [CommRing E] (i : τ) (f g : MvPowerSeries τ E)
    (hf : MvPowerSeries.constantCoeff f = 0) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd := congrArg Finsupp.degree h
  rw [map_add, Finsupp.degree_single] at hd
  by_cases h1 : Finsupp.degree p.1 = 0
  · rw [(Finsupp.degree_eq_zero_iff _).1 h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
  · have h2 : Finsupp.degree p.2 = 0 := by omega
    rw [(Finsupp.degree_eq_zero_iff _).1 h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, mul_zero]

private theorem nz_comp {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (wt : τ → ℤ)
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (h : IsChart0 𝒜 x wt φ) (i : τ) :
    ∃ f ∈ 𝒜 (wt i), MvPowerSeries.coeff (Finsupp.single i 1) (φ f) ≠ 0 := by
  classical
  obtain ⟨f, hf, -⟩ := h.onto i
  rw [← DirectSum.sum_support_decompose 𝒜 f, map_sum, map_sum] at hf
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hf
  have hm := (DirectSum.decompose 𝒜 f j).2
  have hw : wt i = j := by
    by_contra hne
    exact hj (h.graded j _ hm _ (by simpa [Finsupp.weight_single] using hne))
  exact ⟨_, hw ▸ hm, hj⟩

theorem UpperTheory.V.Alg.M.nz_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    1 ≤ Nat.card {i // wt i = -1} → 1 ≤ Nat.card {i // wt i = 1} → SpansCot x 𝒜 (-1) Q.F →
    ∀ a ∈ 𝒜 0, ∃ a' ∈ 𝒜 0, a' - a ∈ Q.ideal ∧ x a' = x a ∧ φ a' ≠ 0 := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hn hp hS a ha
  by_cases h0 : φ a = 0
  swap
  · exact ⟨a, ha, by simp, rfl, h0⟩
  obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.1 hn).1
  obtain ⟨⟨i', hi'⟩⟩ := (Nat.card_pos_iff.1 hp).1
  obtain ⟨f, hf, hf0⟩ := nz_comp 𝒜 x wt φ hφ i
  obtain ⟨g, hg, hg0⟩ := nz_comp 𝒜 x wt φ hφ i'
  rw [hi] at hf
  rw [hi'] at hg
  have hg1 : φ g ≠ 0 := fun h => hg0 (by rw [h, map_zero])
  have hinj : ∀ c : O, c ≠ 0 → ∀ y : FractionRing O, c • y = 0 → y = 0 := fun c hc y hy => by
    rw [Algebra.smul_def] at hy
    exact (mul_eq_zero.1 hy).resolve_left fun h => hc (IsFractionRing.injective O _ (h.trans (map_zero _).symm))
  have hF : ∃ k, φ (Q.F k) ≠ 0 := by
    by_contra hall
    push Not at hall
    let L : A →ₗ[O] FractionRing O :=
      ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap
    have hL : ∀ y, L y = MvPowerSeries.coeff (Finsupp.single i 1) (φ y) := fun _ => rfl
    have hsq : ∀ y ∈ RingHom.ker x ^ 2, L y = 0 := by
      intro y hy
      rw [sq] at hy
      refine Submodule.mul_induction_on hy (fun u hu v hv => ?_) (fun u v hu hv => by rw [map_add, hu, hv, add_zero])
      have hu' : x u = 0 := hu
      have hv' : x v = 0 := hv
      rw [hL, map_mul]
      exact nz_coeff_mul _ _ _ (by rw [hφ.const, hu', map_zero]) (by rw [hφ.const, hv', map_zero])
    have hk : satSq x ≤ LinearMap.ker L := by
      rintro y ⟨c, hc, hy⟩
      have := hsq _ hy
      rw [map_smul] at this
      exact hinj c hc _ this
    have hsp : cotSpan x Q.F ≤ LinearMap.ker ((satSq x).liftQ L hk) := by
      rw [cotSpan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      show L (Q.F k) = 0
      rw [hL, hall k, map_zero]
    obtain ⟨c, hc, hcf⟩ := hS ((satSq x).mkQ f) ⟨f, ⟨hf, hW.fixed (-1) (by norm_num) f hf⟩, rfl⟩
    have := hsp hcf
    rw [LinearMap.mem_ker, map_smul] at this
    exact hf0 (hinj c hc _ this)
  obtain ⟨k, hk⟩ := hF
  have hm : g * Q.F k ∈ 𝒜 0 := by simpa using SetLike.GradedMul.mul_mem hg (Q.hF k)
  refine ⟨a + g * Q.F k, add_mem ha hm, ?_, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [map_add, map_mul, hW.fixed 1 one_ne_zero g hg, zero_mul, add_zero]
  · rw [map_add, h0, zero_add, map_mul]
    exact mul_ne_zero hg1 hk
