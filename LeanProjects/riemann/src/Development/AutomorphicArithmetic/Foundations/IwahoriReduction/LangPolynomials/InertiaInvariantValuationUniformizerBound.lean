import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Ramification
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem unramified_uniformizer_divides {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (π : 𝓞 K) (p : Ideal (𝓞 K)) [p.IsPrime] (hp : p = Ideal.span {π}) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver p]
    (h : Algebra.IsUnramifiedAt (𝓞 K) P) (x : 𝓞 E) (hx : x ∈ P) :
    ∃ t y : 𝓞 E, t ∉ P ∧ t * x = algebraMap (𝓞 K) (𝓞 E) π * y := by
  letI := Localization.AtPrime.algebraOfLiesOver p P
  have h2 := ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 K) p P).1 h).2
  have h3 : algebraMap (𝓞 E) (Localization.AtPrime P) x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P x).2 hx
  rw [← h2] at h3
  have h4 : Ideal.map (algebraMap (𝓞 K) (Localization.AtPrime P)) p =
      Ideal.span {algebraMap (𝓞 K) (Localization.AtPrime P) π} := by
    rw [hp, Ideal.map_span, Set.image_singleton]
  rw [h4, Ideal.mem_span_singleton'] at h3
  obtain ⟨z, hz⟩ := h3
  obtain ⟨⟨y, t⟩, hyt⟩ := IsLocalization.surj P.primeCompl z
  refine ⟨t, y, t.2, ?_⟩
  apply IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  simp only at hyt
  rw [map_mul, map_mul, ← hz, ← hyt, ← IsScalarTower.algebraMap_apply]
  ring

private theorem valuation_le_uniformizer_div {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (u : HeightOneSpectrum (𝓞 E)) (hu : IsPlaceOver A u) (π : 𝓞 E)
    (h : ∀ x ∈ u.asIdeal, ∃ t y : 𝓞 E, t ∉ u.asIdeal ∧ t * x = π * y) (z : E)
    (hz : A.valuation (algebraMap E Ω z) < 1) :
    A.valuation (algebraMap E Ω z) ≤ A.valuation (algebraMap E Ω (π : E)) := by
  have h1 : ∀ s : 𝓞 E, s ∉ u.asIdeal → A.valuation (algebraMap E Ω (s : E)) = 1 := fun s hs =>
    le_antisymm (CompanionTheory.FamInh.val_int_le_one A s) (not_lt.1 ((hu s).not.2 hs))
  obtain ⟨n, d, e | e⟩ := u.exists_primeCompl_mul_eq_or_mul_eq z
  · have e' : z * ((d : 𝓞 E) : E) = (n : E) := e
    have h2 : A.valuation (algebraMap E Ω z) = A.valuation (algebraMap E Ω (n : E)) := by
      rw [← e', map_mul, map_mul, h1 d d.2, mul_one]
    obtain ⟨t, y, ht, e2⟩ := h n ((hu n).1 (h2 ▸ hz))
    have e3 : (t : E) * (n : E) = (π : E) * (y : E) := by exact_mod_cast congrArg (fun a : 𝓞 E => (a : E)) e2
    have h3 := congrArg (fun a : E => A.valuation (algebraMap E Ω a)) e3
    simp only [map_mul] at h3
    rw [h1 t ht, one_mul] at h3
    rw [h2, h3]
    exact mul_le_of_le_one_right' (CompanionTheory.FamInh.val_int_le_one A y)
  · have e' : z * (n : E) = ((d : 𝓞 E) : E) := e
    have h2 := h1 d d.2
    rw [← e', map_mul, map_mul] at h2
    exact absurd h2 ((mul_le_of_le_one_right' (CompanionTheory.FamInh.val_int_le_one A n)).trans_lt hz).ne

private theorem valuation_le_uniformizer_inertia {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (hv : IsPlaceOver A v) (π : 𝓞 K)
    (hπ : v.asIdeal = Ideal.span {π}) (x : Ω) (hx : ∀ s ∈ Ine (F := K) A, s x = x) (h1 : A.valuation x < 1) :
    A.valuation x ≤ A.valuation (algebraMap K Ω (π : K)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : IsGalois K Ω := {}
  let M : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K ({x} : Set Ω)).toIntermediateField
  have hxM : x ∈ M := FiniteGaloisIntermediateField.subset_adjoin K ({x} : Set Ω) rfl
  haveI : NumberField M := NumberField.of_module_finite K M
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := K) M
  haveI : IsAlgClosure M Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨w, hw, hwv⟩ := CompanionTheory.FamInh.exists_place_between (L := M) hv
  let E : IntermediateField K M := IntermediateField.fixedField (w.asIdeal.inertia Gal(M/K))
  haveI : NumberField E := NumberField.of_module_finite K E
  have hxE : (⟨x, hxM⟩ : M) ∈ E := by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := CompanionTheory.FamInh.exists_lift_ine hw hτ
    apply (algebraMap M Ω).injective
    exact (AlgEquiv.restrictNormal_commutes σ M _).trans (hx σ hσ)
  have hun : Algebra.IsUnramifiedAt (𝓞 K) (w.asIdeal.under (𝓞 E)) :=
    (GroundTheory.ProfCoh.isUnramifiedAt_under_iff_inertia (F := K) (E := E) (M := M) w.asIdeal).2
      fun σ hσ y => (IntermediateField.mem_fixedField_iff _ _).1 y.2 σ hσ
  have hu : IsPlaceOver A (w.under (𝓞 E)) := fun y => by
    have := hw (algebraMap (𝓞 E) (𝓞 M) y)
    exact this
  haveI : (w.asIdeal.under (𝓞 E)).LiesOver v.asIdeal := inferInstance
  have := valuation_le_uniformizer_div A (w.under (𝓞 E)) hu (algebraMap (𝓞 K) (𝓞 E) π)
    (unramified_uniformizer_divides π v.asIdeal hπ (w.asIdeal.under (𝓞 E)) hun) ⟨_, hxE⟩ h1
  exact this

theorem UpperTheory.Kd.C7.inertia_invariant_valuation_uniformizer_bound :
    UpperTheory.Kd.C7.FixedIntegersIsUnitOfNotMemPrimeSpan := by
  intro l hl _ Ω _ _ _ A ⟨v, hv, hlv⟩ x hx
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hpr : Prime ((l : ℕ) : 𝓞 ℚ) := by
    have h0 : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
    have := (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm).2 h0
    simpa using this
  have hπ : v.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
    have hm : (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal :=
      ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr).isMaximal (by simpa using hpr.ne_zero)
    exact (hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hlv)).symm
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  by_cases h1 : A.valuation (x : Ω) < 1
  · exfalso
    have h2 := valuation_le_uniformizer_inertia A v hv _ hπ x x.2.2 h1
    have h3 : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [h3] at h2
    have h4 : (x : Ω) / l ∈ A := by
      rw [← A.valuation_le_one_iff, map_div₀]
      exact div_le_one_of_le₀ h2 zero_le
    refine hx (Ideal.mem_span_singleton'.2 ⟨⟨(x : Ω) / l, h4, fun s hs => ?_⟩, Subtype.ext ?_⟩)
    · rw [map_div₀, x.2.2 s hs, map_natCast]
    · push_cast
      exact div_mul_cancel₀ _ hl0
  · have h2 : A.valuation (x : Ω) = 1 := le_antisymm ((A.valuation_le_one_iff _).2 x.2.1) (not_lt.1 h1)
    have h0 : (x : Ω) ≠ 0 := by
      intro h
      rw [h, map_zero] at h2
      exact zero_ne_one h2
    have h4 : (x : Ω)⁻¹ ∈ A := by
      rw [← A.valuation_le_one_iff, map_inv₀, h2, inv_one]
    refine IsUnit.of_mul_eq_one ⟨(x : Ω)⁻¹, h4, fun s hs => ?_⟩ (Subtype.ext ?_)
    · rw [map_inv₀, x.2.2 s hs]
    · exact mul_inv_cancel₀ h0
