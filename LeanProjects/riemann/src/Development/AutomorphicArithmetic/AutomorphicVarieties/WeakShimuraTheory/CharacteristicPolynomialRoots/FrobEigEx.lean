import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

open Pointwise in
private theorem frob_back {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {q : ℕ}
    {g σ : G F Ω} (hσ : IsFrob (F := F) (g • A) q σ) : IsFrob (F := F) A q (g⁻¹ * σ * g) := by
  have key : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation (g⁻¹ y) < 1 := by
    intro y
    rw [valuation_lt_one_iff', valuation_lt_one_iff',
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simp [AlgEquiv.smul_def, map_inv₀]
  refine ⟨?_, fun x hx => ?_⟩
  · have hs : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, hs, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [AlgEquiv.smul_def] using hx
    have h := hσ.2 (g x) hx'
    rw [key] at h
    convert h using 2
    simp [map_sub, map_pow, AlgEquiv.mul_apply]

private theorem frob_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {q : ℕ}
    {σ τ : G F Ω} (hσ : IsFrob (F := F) A q σ) (hτ : IsFrob (F := F) A q τ) : σ⁻¹ * τ ∈ Ine (F := F) A := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hσ.1) hτ.1, fun x hx => ?_⟩
  have h1 : A.valuation (τ x - σ x) < 1 := by
    have h := Valuation.map_sub_lt A.valuation (hτ.2 x hx) (hσ.2 x hx)
    rwa [sub_sub_sub_cancel_right] at h
  have hd : σ⁻¹ ∈ Dec (F := F) A := Subgroup.inv_mem _ hσ.1
  rw [← valuation_apply_lt_one_iff hd] at h1
  convert h1 using 2
  simp [map_sub, AlgEquiv.mul_apply]

theorem UpperTheory.V.Ws.Pu.frobEigEx :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} (ι : PadicAlgCl l ≃+* ℂ) (ρ : G F Ω →* GL (Fin n) (PadicAlgCl l)) (w : HeightOneSpectrum (𝓞 F)), (∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := F) A, ρ s = 1) → ∃ b, Af.FrobEig ι ρ w b := by
  intro F Ω _ _ _ _ _ l _ n ι ρ w hI
  obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ₀, hσ₀⟩ := exists_isFrob (F := F) hA₀
  set p := ((ρ σ₀⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)).charpoly.map
    ι.toRingHom with hp
  refine ⟨p.roots, fun A hA => ⟨hI A hA, fun σ hσ => ?_⟩⟩
  have hpm : p.Monic := (Matrix.charpoly_monic _).map _
  rw [prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpm IsAlgClosed.card_roots_eq_natDegree]
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver hA₀ hA
  have hb := frob_back hσ
  have h1 := hI A₀ hA₀ _ (frob_ine hσ₀ hb)
  rw [map_mul, map_inv] at h1
  have h2 : ρ (g⁻¹ * σ * g) = ρ σ₀ := (inv_mul_eq_one.mp h1).symm
  have h3 : ρ σ⁻¹ = ρ g * ρ σ₀⁻¹ * (ρ g)⁻¹ := by
    have e : σ⁻¹ = g * (g⁻¹ * σ * g)⁻¹ * g⁻¹ := by group
    rw [e, map_mul, map_mul, map_inv, map_inv, h2, map_inv]
  rw [hp, h3, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
