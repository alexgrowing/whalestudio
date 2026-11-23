import Mathlib
open IsLocalRing Polynomial

namespace GlobalTheory.Izumi

theorem exists_dominating_of_residue_map {R S : Type} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] (j : R →+* S) (hj : Function.Injective j)
    (φ : S →+* ResidueField R) (hφ : ∀ r, φ (j r) = residue R r) (f G : R) (u : S)
    (hu : φ u = 0) (hf : j f = j G * u) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
      (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧
      (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨j r, hφ r⟩
  haveI hmax : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  let B := Localization.AtPrime (RingHom.ker φ)
  have hmem : ∀ s : S, algebraMap S B s ∈ maximalIdeal B ↔ φ s = 0 := fun s => by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff B (RingHom.ker φ), RingHom.mem_ker]
  haveI : IsNoetherianRing B :=
    IsLocalization.isNoetherianRing (RingHom.ker φ).primeCompl B inferInstance
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap S B).comp j, ?_, ⟨fun r hr => ?_⟩, fun b => ?_, algebraMap S B u,
    (hmem u).2 hu, ?_⟩
  · exact (IsLocalization.injective B (RingHom.ker φ).primeCompl_le_nonZeroDivisors).comp hj
  · by_contra h
    have h1 : φ (j r) = 0 := by
      rw [hφ, residue_eq_zero_iff]; exact h
    exact (hmem _).2 h1 hr
  · obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker φ).primeCompl b
    have ht : φ t ≠ 0 := t.2
    obtain ⟨r, hr⟩ := residue_surjective (φ s / φ t)
    refine ⟨r, ?_⟩
    have hunit : IsUnit (algebraMap S B t) := IsLocalization.map_units B t
    rw [← Ideal.unit_mul_mem_iff_mem _ hunit, mul_sub]
    dsimp only
    rw [IsLocalization.mk'_spec', RingHom.comp_apply, ← map_mul, ← map_sub, hmem, map_sub,
      map_mul, hφ, hr, mul_div_cancel₀ _ ht, sub_self]
  · simp [hf]

theorem coeff_zero_mem_maximalIdeal_of_aeval_div {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsIntegrallyClosed R] (f G : R) (h : G ∉ Ideal.span {f}) (P : R[X])
    (hP : aeval (algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G) P = 0) :
    P.coeff 0 ∈ maximalIdeal R := by
  by_contra hc
  have hunit : IsUnit (P.coeff 0) := by
    simpa [mem_maximalIdeal] using hc
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hG : G ≠ 0 := by rintro rfl; exact h (zero_mem _)
  have hG' : algebraMap R (FractionRing R) G ≠ 0 := (map_ne_zero_iff _ hinj).2 hG
  have hf : f ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, ← coeff_zero_eq_aeval_zero'] at hP
    exact hunit.ne_zero ((map_eq_zero_iff _ hinj).1 hP)
  have hf' : algebraMap R (FractionRing R) f ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
  set u := algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G with hu
  have hu0 : u ≠ 0 := div_ne_zero hf' hG'
  letI := invertibleOfNonzero hu0
  have hrev : aeval (⅟u) P.reverse = 0 := by
    rw [aeval_def, eval₂_reverse_eq_zero_iff]; exact hP
  have hint := isIntegral_leadingCoeff_smul P.reverse (⅟u) hrev
  rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero hunit.ne_zero] at hint
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  apply h
  rw [← Ideal.unit_mul_mem_iff_mem _ hunit, Ideal.mem_span_singleton']
  refine ⟨r, hinj ?_⟩
  rw [map_mul, map_mul, hr, invOf_eq_inv, hu, Algebra.smul_def]
  field_simp

theorem exists_dominating_eq_mul_of_not_mem_span :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
      [IsIntegrallyClosed R] (f G : R), G ∉ Ideal.span {f} →
      ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
        (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧
        (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by
  intro R _ _ _ _ _ f G h
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hG : G ≠ 0 := by rintro rfl; exact h (zero_mem _)
  have hG' : algebraMap R (FractionRing R) G ≠ 0 := (map_ne_zero_iff _ hinj).2 hG
  let u := algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G
  let e : R[X] →+* FractionRing R := (aeval u : R[X] →ₐ[R] FractionRing R)
  have he : ∀ P, e P = aeval u P := fun _ => rfl
  haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  let φ : (R[X] ⧸ RingHom.ker e) →+* ResidueField R :=
    Ideal.Quotient.lift _ ((residue R).comp constantCoeff) fun P hP => by
      rw [RingHom.comp_apply, residue_eq_zero_iff]
      exact coeff_zero_mem_maximalIdeal_of_aeval_div f G h P hP
  refine exists_dominating_of_residue_map ((Ideal.Quotient.mk (RingHom.ker e)).comp C) ?_ φ ?_
    f G (Ideal.Quotient.mk _ X) ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro r hr
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker, he, aeval_C] at hr
    exact (map_eq_zero_iff _ hinj).1 hr
  · intro r; simp [φ]
  · simp [φ]
  · rw [RingHom.comp_apply, RingHom.comp_apply, ← map_mul, Ideal.Quotient.eq, RingHom.mem_ker, he]
    simp only [map_sub, map_mul, aeval_C, aeval_X, u]
    field_simp
    ring

end GlobalTheory.Izumi
