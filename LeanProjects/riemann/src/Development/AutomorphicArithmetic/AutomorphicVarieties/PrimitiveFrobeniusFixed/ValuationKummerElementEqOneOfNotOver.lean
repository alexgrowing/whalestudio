import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem val_count_int {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    v.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))) := by
  have h1 : v.valuation K (a : K) = v.intValuation a := v.valuation_of_algebraMap a
  have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
      = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_span_singleton a).symm
  rw [h1, h2, v.intValuation_if_neg ha, FractionalIdeal.count_coe K v (by simpa using ha)]

private theorem val_count {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx
    simp [← e]
  have e' : x * (b : K) = (a : K) := by
    rw [← e]; exact div_mul_cancel₀ _ hbK
  have h1 := val_count_int v a ha0
  have h2 := val_count_int v b hb0
  rw [← e', map_mul, h2, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbK), neg_add, WithZero.exp_add] at h1
  exact mul_right_cancel₀ WithZero.exp_ne_zero h1

theorem UpperTheory.valuation_kummerElement_eq_one_of_not_over :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b r : ℕ) (v w : HeightOneSpectrum (𝓞 K)) (X : K), IsX M K b v.asIdeal X → (r : 𝓞 K) ∈ v.asIdeal → (r : 𝓞 K) ∉ w.asIdeal → w.valuation K X = 1 := by
  intro M _ K _ _ _ b r v w X hX hv hw
  have hX0 : X ≠ 0 := left_ne_zero_of_mul_eq_one hX.1
  let P : (ZMod M)ˣ → HeightOneSpectrum (𝓞 K) := fun t =>
    HeightOneSpectrum.comap (sgO M K t : 𝓞 K →+* 𝓞 K) (sgO M K t).surjective v
  have hP : ∀ t, (P t).asIdeal = conjI M K v.asIdeal t := fun t => rfl
  have hne : ∀ t, P t ≠ w := by
    intro t h
    apply hw
    rw [← h, hP, mem_conjI, map_natCast]
    exact hv
  rw [val_count w X hX0, hX.2, FractionalIdeal.count_prod]
  · rw [Finset.sum_eq_zero, neg_zero, WithZero.exp_zero]
    intro t _
    rw [FractionalIdeal.count_zpow, ← hP, FractionalIdeal.count_maximal_coprime K w (hne t), mul_zero]
  · intro t _
    apply zpow_ne_zero
    rw [← hP]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr (P t).ne_bot
