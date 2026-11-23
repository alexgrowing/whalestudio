import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem val_top {Ω : Type} [Field Ω] {x : Ω} (h : (⊤ : ValuationSubring Ω).valuation x < 1) : x = 0 := by
  by_contra hx
  have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
  rw [← map_mul, mul_inv_cancel₀ hx, map_one] at h2
  exact lt_irrefl _ h2

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_place (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (A : ValuationSubring Ω) (hA : A ≠ ⊤) : ∃ v : HeightOneSpectrum (𝓞 K),
      ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ v.asIdeal := by
  have hm : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x =>
    (A.valuation_le_one_iff _).1 (int_le A (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom))
  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hm
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  refine ⟨⟨P, inferInstance, fun h0 => hA ?_⟩, hP⟩
  rw [eq_top_iff]
  intro x _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have h1 : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).2 inferInstance
  have h2 : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ K Ω
  obtain ⟨n, hn, hi⟩ := (h2.isAlgebraic x).exists_integral_multiple
  have h3 : ¬ A.valuation (algebraMap K Ω ((n : 𝓞 K) : K)) < 1 := by
    rw [hP, h0, Ideal.mem_bot]
    exact Int.cast_ne_zero.2 hn
  have h4 : A.valuation (n : Ω) = 1 :=
    le_antisymm (int_le A (isIntegral_algebraMap (R := ℤ) (x := n))) (by simpa using h3)
  have h5 := int_le A hi
  rw [zsmul_eq_mul, map_mul, h4, one_mul] at h5
  exact (A.valuation_le_one_iff x).1 h5

theorem UpperTheory.V.Kum.placeDict :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Ine (F := K) (⊤ : ValuationSubring Ω) = ⊥ ∧ (∀ A : ValuationSubring Ω, A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v) ∧
    (∀ (A : ValuationSubring Ω) (N : ℕ), N ≠ 0 → A.valuation (N : Ω) < 1 → A ≠ ⊤) ∧
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (N : ℕ), IsPlaceOver A v → (A.valuation (N : Ω) < 1 ↔ v ∈ Above K N) := by
  intro K Ω _ _ _ _ _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext x
    have h := hg.2 x ((ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _))
    exact sub_eq_zero.1 (val_top h)
  · intro A hA
    exact exists_place K Ω A hA
  · rintro A N hN h rfl
    exact hN (Nat.cast_eq_zero.1 (val_top h))
  · intro A v N hv
    have h := hv (N : 𝓞 K)
    have e : algebraMap K Ω ((N : 𝓞 K) : K) = (N : Ω) := by simp
    rw [← e]
    exact h
