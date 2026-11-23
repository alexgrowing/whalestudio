import Mathlib

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

section krull

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]

theorem isOpen_setOf_apply (x : Ω) (P : Ω → Prop) : IsOpen {τ : Ω ≃ₐ[F] Ω | P (τ x)} := by
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional hx
  have hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  rw [isOpen_iff_forall_mem_open]
  intro τ hτ
  refine ⟨(fun σ => τ⁻¹ * σ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω)),
    ?_, ?_, ?_⟩
  · intro σ hσ
    have hσ' : τ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup := hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ'
    have h1 := hσ' x (IntermediateField.mem_adjoin_simple_self F x)
    have h2 : σ x = τ x := by
      calc σ x = (τ * (τ⁻¹ * σ)) x := by rw [mul_inv_cancel_left]
        _ = τ ((τ⁻¹ * σ) x) := by rw [AlgEquiv.mul_apply]
        _ = τ x := by rw [h1]
    show P (σ x)
    rw [h2]
    exact hτ
  · exact hH.preimage (continuous_const.mul continuous_id)
  · show τ⁻¹ * τ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _

theorem isClosed_setOf_apply (x : Ω) (P : Ω → Prop) : IsClosed {τ : Ω ≃ₐ[F] Ω | P (τ x)} := by
  rw [← isOpen_compl_iff]
  exact isOpen_setOf_apply x (fun y => ¬ P y)

end krull

section roots

variable {Ω : Type*} [Field Ω]

theorem eq_one_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {ξ : Ω} (hξ : ξ ^ N = 1) (h : A.valuation (ξ - 1) < 1) : ξ = 1 := by
  have hξ1 : A.valuation ξ ≤ 1 := by
    have h2 := Valuation.map_add A.valuation (ξ - 1) 1
    rw [sub_add_cancel, Valuation.map_one] at h2
    exact h2.trans (max_le h.le le_rfl)
  have hpow : ∀ j : ℕ, A.valuation (ξ ^ j) ≤ 1 := fun j => by
    rw [Valuation.map_pow]
    exact pow_le_one' hξ1 j
  have hgeom : ∀ i : ℕ, A.valuation (ξ ^ i - 1) < 1 := by
    intro i
    rw [← geom_sum_mul, Valuation.map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' ?_) h
    exact Valuation.map_sum_le _ (fun j _ => hpow j)
  by_contra hne
  have h3 := geom_sum_mul ξ N
  rw [hξ, sub_self] at h3
  have hS := (mul_eq_zero.1 h3).resolve_right (fun h4 => hne (sub_eq_zero.1 h4))
  have h5 := Valuation.map_sum_lt A.valuation (s := Finset.range N) (f := fun i => ξ ^ i - 1)
    one_ne_zero (fun i _ => hgeom i)
  rw [Finset.sum_sub_distrib, hS] at h5
  apply hN
  simpa using h5

theorem valuation_eq_one_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN0 : N ≠ 0) {b : Ω}
    (hb : b ^ N = 1) : A.valuation b = 1 := by
  have h1 : A.valuation b ^ N = 1 := by rw [← Valuation.map_pow, hb, Valuation.map_one]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := Nat.exists_eq_succ_of_ne_zero hN0
  rw [pow_succ] at h1
  rcases lt_trichotomy (A.valuation b) 1 with hlt | heq | hgt
  · exfalso
    have h2 : A.valuation b ^ M * A.valuation b ≤ A.valuation b :=
      mul_le_of_le_one_left' (pow_le_one' hlt.le M)
    rw [h1] at h2
    exact absurd hlt (not_lt.2 h2)
  · exact heq
  · exfalso
    have h2 : A.valuation b ≤ A.valuation b ^ M * A.valuation b :=
      le_mul_of_one_le_left' (one_le_pow_of_one_le' hgt.le M)
    rw [h1] at h2
    exact absurd hgt (not_lt.2 h2)

theorem eq_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {a b : Ω} (ha : a ^ N = 1) (hb : b ^ N = 1) (h : A.valuation (a - b) < 1) : a = b := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    apply hN
    simp
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp [hN0] at hb
  have hvb := valuation_eq_one_of_pow_eq_one A hN0 hb
  have hξ : (a / b) ^ N = 1 := by rw [div_pow, ha, hb, div_one]
  have hξ1 : A.valuation (a / b - 1) < 1 := by
    rw [div_sub_one hb0, Valuation.map_div, hvb, div_one]
    exact h
  have h2 := eq_one_of_pow_eq_one A hN hξ hξ1
  rwa [div_eq_one_iff_eq hb0] at h2

end roots

section exists_place

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem exists_valuationSubring_over (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A : ValuationSubring Ω, ∀ x : 𝓞 F,
      A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal := by
  classical
  let φ : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F)
  have hφ : Function.Injective φ :=
    (algebraMap F Ω).injective.comp (IsFractionRing.injective (𝓞 F) F)
  have hu : ∀ y : v.asIdeal.primeCompl, IsUnit (φ y) := by
    intro y
    refine isUnit_iff_ne_zero.2 ?_
    intro h0
    apply y.2
    have h1 : (y : 𝓞 F) = 0 := hφ (h0.trans (map_zero φ).symm)
    rw [h1]
    exact v.asIdeal.zero_mem
  let f : (Localization.AtPrime v.asIdeal) →+* Ω := IsLocalization.lift (M := v.asIdeal.primeCompl) hu
  have hf : ∀ z : 𝓞 F, f (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) z) = φ z := fun z => IsLocalization.lift_eq hu z
  have hfi : Function.Injective f := by
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro hab
      rw [IsLocalization.injective (M := v.asIdeal.primeCompl) (S := (Localization.AtPrime v.asIdeal))
        (Ideal.primeCompl_le_nonZeroDivisors _) hab]
    · intro hab
      rw [hφ hab]
  obtain ⟨B, hB⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range f)
  rw [LocalSubring.le_def] at hB
  obtain ⟨hle, hloc⟩ := hB
  haveI := hloc
  refine ⟨B, fun x => ?_⟩
  have hmem : φ x ∈ B := hle ⟨algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x, hf x⟩
  let bx : B := ⟨φ x, hmem⟩
  have hv : B.valuation (algebraMap F Ω (x : F)) = B.valuation (bx : Ω) := rfl
  rw [hv, ← ValuationSubring.valuation_lt_one_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hx
    apply hnu
    have h1 : IsUnit (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) :=
      IsLocalization.map_units (Localization.AtPrime v.asIdeal) (⟨x, hx⟩ : v.asIdeal.primeCompl)
    have h3 := (h1.map f.rangeRestrict).map (Subring.inclusion hle)
    rw [show f.rangeRestrict (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) =
      (⟨φ x, ⟨_, hf x⟩⟩ : f.range) from Subtype.ext (hf x)] at h3
    exact h3
  · intro hx hu'
    have h1 := isUnit_of_map_unit (Subring.inclusion hle) ⟨φ x, ⟨_, hf x⟩⟩ hu'
    obtain ⟨w, hw⟩ := h1.exists_right_inv
    obtain ⟨r, hr⟩ := w.2
    have h4 : f (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x * r) = f 1 := by
      rw [map_mul, hf, hr, map_one]
      exact congrArg Subtype.val hw
    have h5 : IsUnit (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) := ⟨⟨_, r, hfi h4, (mul_comm _ _).trans (hfi h4)⟩, rfl⟩
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime v.asIdeal) v.asIdeal x).1 h5 hx

end exists_place

end ReciprocityTheory.Gal
