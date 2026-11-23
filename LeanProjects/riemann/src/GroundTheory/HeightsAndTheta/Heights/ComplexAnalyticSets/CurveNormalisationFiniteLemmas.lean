import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.LocalIntegralClosureChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets FieldNumbers

noncomputable section

theorem exists_finset_span_integral_of_div (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O Ω : Type}
    [CommRing O] [Field Ω] [Algebra O Ω] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f)
    (hΩ : ∀ x : Ω, ∃ a b : O, x = algebraMap O Ω a / algebraMap O Ω b) :
    ∃ t : Finset Ω, ∀ x : Ω, IsIntegral O x → x ∈ Submodule.span O (t : Set Ω) := by
  let ψ : MvPolynomial (Fin n) ℂ →+* Ω := (algebraMap O Ω).comp φ
  let _ : Algebra ℂ Ω := (ψ.comp C).toAlgebra
  let S : Set Ω := Set.range fun i ↦ ψ (X i)
  have hpoly : ∀ f, ψ f ∈ Algebra.adjoin ℂ S := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => exact Subalgebra.algebraMap_mem _ c
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f i hf => rw [map_mul]; exact mul_mem hf (Algebra.subset_adjoin ⟨i, rfl⟩)
  let A : Subalgebra ℂ Ω :=
    { toSubsemiring := (algebraMap O Ω).rangeS, algebraMap_mem' := fun c ↦ ⟨φ (C c), rfl⟩ }
  have hRA : Algebra.adjoin ℂ S ≤ A := Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact ⟨φ (X i), rfl⟩)
  have hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin ℂ S, ∃ d ∈ Algebra.adjoin ℂ S, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹ := by
    rintro _ ⟨o, rfl⟩
    obtain ⟨f, s, hs, ho⟩ := hφ o
    refine ⟨ψ f, hpoly f, ψ s, hpoly s, (hs.map (algebraMap O Ω)).ne_zero, ⟨↑hs.unit⁻¹, ?_⟩, ?_⟩
    · change algebraMap O Ω ↑hs.unit⁻¹ = (algebraMap O Ω (φ s))⁻¹
      rw [map_units_inv, IsUnit.unit_spec]
    · refine (eq_mul_inv_iff_mul_eq₀ (hs.map (algebraMap O Ω)).ne_zero).2 ?_
      change algebraMap O Ω o * algebraMap O Ω (φ s) = algebraMap O Ω (φ f)
      rw [← map_mul, ho]
  have hE : ∀ x : Ω, x ∈ IntermediateField.adjoin ℂ S := by
    have hA : ∀ a ∈ A, a ∈ IntermediateField.adjoin ℂ S := by
      intro a ha
      obtain ⟨r, hr, d, hd, -, -, rfl⟩ := hloc a ha
      exact mul_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hr)
        (inv_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hd))
    intro x
    obtain ⟨a, b, rfl⟩ := hΩ x
    exact div_mem (hA _ ⟨a, rfl⟩) (hA _ ⟨b, rfl⟩)
  have hfin : FiniteDimensional (IntermediateField.adjoin ℂ S)
      (IntermediateField.extendScalars (le_refl (IntermediateField.adjoin ℂ S))) := by
    rw [IntermediateField.extendScalars_self]; infer_instance
  obtain ⟨t, -, ht⟩ := exists_finset_integral_span hN (Set.finite_range _) A _ hRA hloc le_rfl hfin
  let _ : Algebra O A := ((algebraMap O Ω).codRestrict A fun o ↦ (⟨o, rfl⟩ : algebraMap O Ω o ∈ (algebraMap O Ω).rangeS)).toAlgebra
  have : IsScalarTower O A Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsur : Function.Surjective (algebraMap O A) := by rintro ⟨_, o, rfl⟩; exact ⟨o, rfl⟩
  refine ⟨t, fun x hx ↦ ?_⟩
  rw [← Submodule.restrictScalars_span O A hsur]
  exact ht x (hE x) hx.tower_top

theorem exists_algHom_span_of_mem_minimalPrimes (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ}
    {O : Type} [CommRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) {p : Ideal O} (hp : p ∈ minimalPrimes O) :
    ∃ g : FractionRing O →ₐ[O] FractionRing (O ⧸ p), ∃ t : Finset (FractionRing (O ⧸ p)),
      ∀ x : FractionRing O, IsIntegral O x → g x ∈ Submodule.span O (t : Set (FractionRing (O ⧸ p))) := by
  have := Ideal.IsMinimalPrime.isPrime hp
  have hu : ∀ y : nonZeroDivisors O, IsUnit (Algebra.ofId O (FractionRing (O ⧸ p)) y) := by
    intro y
    refine IsUnit.mk0 _ fun h ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes ?_ hp y.2
    have h' : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p y) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by rw [map_zero]; exact h
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ h')
  obtain ⟨t, ht⟩ := exists_finset_span_integral_of_div hN φ hφ (Ω := FractionRing (O ⧸ p)) fun x ↦ by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O ⧸ p) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨a, b, rfl⟩
  exact ⟨IsLocalization.liftAlgHom (M := nonZeroDivisors O) hu, t, fun x hx ↦ ht _ (hx.map _)⟩

theorem finite_integralClosure_of_isReduced (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O : Type}
    [CommRing O] [IsReduced O] [IsNoetherianRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) :
    Module.Finite O (integralClosure O (FractionRing O)) := by
  have := (minimalPrimes.finite_of_isNoetherianRing O).to_subtype
  choose g t ht using fun p : minimalPrimes O ↦ exists_algHom_span_of_mem_minimalPrimes hN φ hφ p.2
  let F : integralClosure O (FractionRing O) →ₗ[O]
      ((p : minimalPrimes O) → Submodule.span O (t p : Set (FractionRing (O ⧸ (p : Ideal O))))) :=
    LinearMap.pi fun p ↦ LinearMap.codRestrict _
      ((g p).toLinearMap ∘ₗ (integralClosure O (FractionRing O)).val.toLinearMap) fun x ↦ ht p x x.2
  refine Module.Finite.of_injective F ((injective_iff_map_eq_zero F).2 fun x hx ↦ ?_)
  have h0 : ∀ p : minimalPrimes O, g p x = 0 := fun p ↦ congrArg Subtype.val (congr_fun hx p)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) (x : FractionRing O)
  have ha : a ∈ sInf (minimalPrimes O) := by
    refine Ideal.mem_sInf.2 fun p hp ↦ ?_
    have := Ideal.IsMinimalPrime.isPrime hp
    have e : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p a) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by
      rw [map_zero]
      change algebraMap O (FractionRing (O ⧸ p)) a = 0
      rw [← (g ⟨p, hp⟩).commutes, ← hab, map_mul, h0, zero_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ e)
  rw [Ideal.sInf_minimalPrimes, Ideal.mem_radical_iff] at ha
  obtain ⟨k, hk⟩ := ha
  have ha0 : a = 0 := IsNilpotent.eq_zero ⟨k, by simpa using hk⟩
  rw [ha0, map_zero, (IsLocalization.map_units (FractionRing O) b).mul_left_eq_zero] at hab
  exact Subtype.ext hab

theorem isReduced_curveLocalRing {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (h : IsRadicalAt I q) : IsReduced (curveLocalRing I q) := by
  refine (Ideal.isRadical_iff_quotient_reduced _).1 ?_
  rw [Ideal.IsRadical, ← IsLocalization.map_radical (RingHom.ker (eval q)).primeCompl]
  refine Ideal.map_le_iff_le_comap.2 fun f hf ↦ ?_
  obtain ⟨s, hs, hsf⟩ := h f hf
  have hu : IsUnit (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) s) :=
    IsLocalization.map_units _ (⟨s, fun h' ↦ hs (RingHom.mem_ker.1 h')⟩ : (RingHom.ker (eval q)).primeCompl)
  exact (Ideal.unit_mul_mem_iff_mem _ hu).1 (by rw [← map_mul]; exact Ideal.mem_map_of_mem _ hsf)

theorem curveLocalRing_eq_div {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (o : curveLocalRing I q) : ∃ f s, IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s) ∧
      o * algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s =
        algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f := by
  obtain ⟨z, rfl⟩ : ∃ z, Ideal.Quotient.mk
      (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))) z = o :=
    Ideal.Quotient.mk_surjective o
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker (eval q)).primeCompl z
  refine ⟨f, s, isUnit_algebraMap_curveLocalRing I q s fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have e := congrArg (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker (eval q))) f s)
  rw [map_mul] at e
  exact e

end

end GroundTheory.Heights₂.Heights
