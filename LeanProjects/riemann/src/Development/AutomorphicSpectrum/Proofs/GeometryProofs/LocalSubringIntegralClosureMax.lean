import Mathlib

namespace GlobalTheory.CompanionTheory.Domination

theorem isUnit_subring_iff {K : Type} [Field K] (D : Subring K) (d : D) :
    IsUnit d ↔ (d : K) ≠ 0 ∧ (d : K)⁻¹ ∈ D := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : ((u : D) : K) * (((u⁻¹ : Dˣ) : D) : K) = 1 := by
      exact_mod_cast congrArg Subtype.val u.mul_inv
    refine ⟨left_ne_zero_of_mul_eq_one h, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h]
    exact ((u⁻¹ : Dˣ) : D).2
  · rintro ⟨h0, h⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, h⟩, Subtype.ext (by simp [h0])⟩

theorem isMaximal_of_comap {K : Type} [Field K] (R T : Subring K) (hRT : R ≤ T)
    (hint : ∀ t ∈ T, IsIntegral R t) (P : Ideal T) [P.IsPrime]
    (hc : (P.comap (Subring.inclusion hRT)).IsMaximal) : P.IsMaximal := by
  let _ : Algebra R T := (Subring.inclusion hRT).toAlgebra
  have : Algebra.IsIntegral R T := ⟨fun t ↦ by
    let f : T →ₐ[R] K := { T.subtype with commutes' := fun r ↦ rfl }
    exact (isIntegral_algHom_iff f Subtype.val_injective).1 (hint t t.2)⟩
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hc

theorem eq_ofPrime {K : Type} [Field K] (T D : Subring K) (P : Ideal T) [P.IsPrime]
    (hP : ∀ t : T, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D)) (hTD : T ≤ D)
    (gen : ∀ a ∈ D, ∃ u ∈ T, ∃ v ∈ T, v ≠ 0 ∧ v⁻¹ ∈ D ∧ a = u / v) :
    D = (LocalSubring.ofPrime T P).toSubring := by
  ext a
  simp only [LocalSubring.ofPrime, LocalSubring.range_toSubring]
  show a ∈ D ↔ a ∈ Set.range _
  rw [Set.mem_range]
  constructor
  · intro ha
    obtain ⟨u, hu, v, hv, h0, hvD, rfl⟩ := gen a ha
    have hvP : (⟨v, hv⟩ : T) ∈ P.primeCompl := by
      show (⟨v, hv⟩ : T) ∉ P
      rw [hP]
      exact not_not.2 ⟨h0, hvD⟩
    refine ⟨IsLocalization.mk' _ (⟨u, hu⟩ : T) (⟨⟨v, hv⟩, hvP⟩ : P.primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    show u = v * (u / v)
    field_simp
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨u, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    have hs : ¬ ((s : T) ∈ P) := s.2
    rw [hP, not_not] at hs
    have key : ∀ z : K, ((u : T) : K) = ((s : T) : K) * z → z ∈ D := by
      intro z hz
      have hz' : z = (u : K) * ((s : T) : K)⁻¹ := by
        rw [hz]
        field_simp [hs.1]
      rw [hz']
      exact D.mul_mem (hTD u.2) hs.2
    dsimp only
    apply key
    exact (IsLocalization.lift_mk'_spec (S := Localization.AtPrime P) (g := T.subtype) _ _ _ _).1 rfl

theorem eq_localisation_integralClosure :
    ∀ {K : Type} [Field K] (R D B : Subring K) [IsLocalRing R] [IsLocalRing D], R ≤ D →
      (∀ r ∈ R, r ≠ 0 → r⁻¹ ∈ D → r⁻¹ ∈ R) → (integralClosure R K).toSubring ≤ D →
      B ≤ (integralClosure R K).toSubring →
      (∀ a ∈ D, ∃ u ∈ B, ∃ v ∈ B, v ≠ 0 ∧ v⁻¹ ∈ D ∧ a = u / v) →
      ∃ (P : Ideal (integralClosure R K).toSubring) (_ : P.IsMaximal),
        D = (LocalSubring.ofPrime _ P).toSubring ∧
        ∀ t : (integralClosure R K).toSubring, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D) := by
  intro K _ R D B _ _ hRD hdom hTD hBT gen
  let P : Ideal (integralClosure R K).toSubring :=
    (IsLocalRing.maximalIdeal D).comap (Subring.inclusion hTD)
  have hP : ∀ t : (integralClosure R K).toSubring, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D) := by
    intro t
    show Subring.inclusion hTD t ∈ IsLocalRing.maximalIdeal D ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_subring_iff]
    rfl
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hRT : R ≤ (integralClosure R K).toSubring := fun r hr ↦ by
    show IsIntegral R (algebraMap R K ⟨r, hr⟩)
    exact isIntegral_algebraMap
  have hint : ∀ t ∈ (integralClosure R K).toSubring, IsIntegral R t := fun t ht ↦ ht
  have hPmax : P.IsMaximal := by
    apply isMaximal_of_comap R _ hRT hint P
    have hc : P.comap (Subring.inclusion hRT) = IsLocalRing.maximalIdeal R := by
      ext r
      rw [Ideal.mem_comap, hP, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_subring_iff]
      show ¬ ((r : K) ≠ 0 ∧ (r : K)⁻¹ ∈ D) ↔ ¬ ((r : K) ≠ 0 ∧ (r : K)⁻¹ ∈ R)
      exact not_congr ⟨fun ⟨h0, h⟩ ↦ ⟨h0, hdom _ r.2 h0 h⟩, fun ⟨h0, h⟩ ↦ ⟨h0, hRD h⟩⟩
    rw [hc]
    exact IsLocalRing.maximalIdeal.isMaximal R
  refine ⟨P, hPmax, ?_, hP⟩
  refine eq_ofPrime _ D P hP hTD fun a ha ↦ ?_
  obtain ⟨u, hu, v, hv, h0, hvD, rfl⟩ := gen a ha
  exact ⟨u, hBT hu, v, hBT hv, h0, hvD, rfl⟩

end GlobalTheory.CompanionTheory.Domination
