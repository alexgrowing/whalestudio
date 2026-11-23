import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEmbeddingOverPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SqrtNegRam

open Polynomial

theorem valuation_natCast_eq {F : Type} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr F) (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    v.valuation F (p : F) = WithZero.exp (-1 : ℤ) := by
  have h2 := GlobalTheory.LamTie.ExpCond.not_mem_sq_of_not_dvd_discr hp hd v hv
  have e : (p : F) = algebraMap (𝓞 F) F (p : 𝓞 F) := by simp
  rw [e, v.valuation_of_algebraMap]
  have h0 : ((p : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hne := v.intValuation_ne_zero _ h0
  have h1 := (v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hv)
  have h2' := mt (v.intValuation_le_pow_iff_mem _ 2).1 h2
  rw [← WithZero.exp_log hne] at h1 h2' ⊢
  rw [WithZero.exp_le_exp] at h1 h2'
  rw [WithZero.exp_inj]
  push_cast at h1 h2'
  omega

theorem valuation_mul_ne_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr F) {δ : Ω}
    (hδ : δ ^ 2 = -(p : Ω)) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) (hA : IsPlaceOver A v) (y : F) (hy : y ≠ 0) :
    A.valuation (algebraMap F Ω y * δ) ≠ 1 := by
  intro h
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v hA
  have hmem : ∀ e : F, algebraMap F Ω e ∈ A ↔ v.valuation F e ≤ 1 := fun e => by
    rw [hι, ι.commutes]; exact GlobalTheory.LocEmbExist.isIntegral_algebraMap_iff v e
  have he : algebraMap F Ω (y ^ 2 * p) = -(algebraMap F Ω y * δ) ^ 2 := by
    rw [mul_pow, hδ, map_mul, map_pow, map_natCast]; ring
  have hw : A.valuation (algebraMap F Ω (y ^ 2 * p)) = 1 := by
    rw [he, Valuation.map_neg, map_pow, h, one_pow]
  have h1 : v.valuation F (y ^ 2 * p) ≤ 1 := (hmem _).1 ((A.valuation_le_one_iff _).1 hw.le)
  have h2 : v.valuation F (y ^ 2 * p)⁻¹ ≤ 1 :=
    (hmem _).1 ((A.valuation_le_one_iff _).1 (by rw [map_inv₀, map_inv₀, hw, inv_one]))
  have hy0 : v.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [map_inv₀] at h2
  rw [map_mul, map_pow, valuation_natCast_eq hp hd v hv, ← WithZero.exp_log hy0,
    ← WithZero.exp_nsmul, ← WithZero.exp_add] at h1 h2
  rw [← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  rw [nsmul_eq_mul] at h1 h2
  push_cast at h1 h2
  omega

end GlobalTheory.SqrtNegRam

namespace GlobalTheory.SqrtNegRam

open Polynomial

theorem sqrt_neg_moved_by_inertia : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ), p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ discr F → ∀ (δ : Ω), δ ^ 2 = -(p : Ω) → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∃ s ∈ Ine (F := F) A, s δ ≠ δ := by
  intro F Ω _ _ _ _ _ p hp _ hd δ hδ v A hv hA
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have KL := valuation_mul_ne_one hp hd hδ hv hA
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    apply hp0
    linear_combination hδ
  set f : F[X] := X ^ 2 + C (p : F) with hfdef
  have hf_root : ∀ x : Ω, aeval x f = 0 ↔ x ^ 2 = -(p : Ω) := by
    intro x
    simp only [hfdef, map_add, map_pow, aeval_X, aeval_C, map_natCast]
    constructor <;> intro h <;> linear_combination h
  have hmon : f.Monic := monic_X_pow_add_C _ two_ne_zero
  have hirr : Irreducible f := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [hfdef, natDegree_X_pow_add_C]; decide
    · intro c hc
      have hc' : (algebraMap F Ω c) ^ 2 = -(p : Ω) := by
        rw [← hf_root, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hc, map_zero]
      have hc0 : c ≠ 0 := by
        rintro rfl
        apply hp0
        rw [map_zero] at hc'
        linear_combination hc'
      have hc1 : (algebraMap F Ω c)⁻¹ * algebraMap F Ω c = 1 :=
        inv_mul_cancel₀ ((_root_.map_ne_zero _).2 hc0)
      have hfac : (algebraMap F Ω c - δ) * (algebraMap F Ω c + δ) = 0 := by
        linear_combination hc' - hδ
      rcases mul_eq_zero.1 hfac with h | h
      · apply KL c⁻¹ (inv_ne_zero hc0)
        rw [map_inv₀, ← sub_eq_zero.1 h, hc1, map_one]
      · apply KL c⁻¹ (inv_ne_zero hc0)
        have e : δ = -(algebraMap F Ω c) := by linear_combination h
        rw [e, mul_neg, map_inv₀, hc1, Valuation.map_neg, map_one]
  have hmin : f = minpoly F δ := minpoly.eq_of_irreducible_of_monic hirr ((hf_root δ).2 hδ) hmon
  have hmin' : f = minpoly F (-δ) :=
    minpoly.eq_of_irreducible_of_monic hirr ((hf_root _).2 (by rw [neg_sq]; exact hδ)) hmon
  obtain ⟨σ₀, hσ₀⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1 (hmin'.symm.trans hmin)
  have hσ₀' : σ₀ δ = -δ := hσ₀
  let M : IntermediateField F Ω := IntermediateField.adjoin F (f.rootSet Ω)
  haveI : Polynomial.IsSplittingField F M f :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : Normal F M := Normal.of_isSplittingField f
  haveI : FiniteDimensional F M := Polynomial.IsSplittingField.finiteDimensional M f
  haveI : IsGalois F M := ⟨⟩
  let τ : M ≃ₐ[F] M := σ₀.restrictNormal M
  have hδM : δ ∈ M := IntermediateField.subset_adjoin _ _
    (by rw [Polynomial.mem_rootSet]; exact ⟨hmon.ne_zero, (hf_root δ).2 hδ⟩)
  have hform : ∀ z ∈ M, ∃ a b : F, z = algebraMap F Ω a + algebraMap F Ω b * δ := by
    intro z hz
    have hz' : z ∈ Algebra.adjoin F (f.rootSet Ω) := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)]
      exact hz
    clear hz
    induction hz' using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Polynomial.mem_rootSet, hf_root] at hx
      have hfx : (x - δ) * (x + δ) = 0 := by linear_combination hx.2 - hδ
      rcases mul_eq_zero.1 hfx with h | h
      · exact ⟨0, 1, by rw [map_zero, map_one]; linear_combination h⟩
      · exact ⟨0, -1, by rw [map_zero, map_neg, map_one]; linear_combination h⟩
    | algebraMap r => exact ⟨r, 0, by rw [map_zero]; ring⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      exact ⟨a + c, b + d, by rw [map_add, map_add]; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      refine ⟨a * c - b * d * p, a * d + b * c, ?_⟩
      simp only [map_add, map_sub, map_mul, map_natCast]
      linear_combination (algebraMap F Ω b * algebraMap F Ω d) * hδ
  have hcond : ∀ x : M, A.valuation (algebraMap M Ω x) ≤ 1 →
      A.valuation (algebraMap M Ω (τ x) - algebraMap M Ω x) < 1 := by
    intro x hx
    rw [AlgEquiv.restrictNormal_commutes]
    obtain ⟨a, b, hab⟩ := hform (algebraMap M Ω x) x.2
    rw [hab] at hx ⊢
    have e : σ₀ (algebraMap F Ω a + algebraMap F Ω b * δ) - (algebraMap F Ω a + algebraMap F Ω b * δ)
        = (-2 : Ω) * (algebraMap F Ω b * δ) := by
      rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hσ₀']; ring
    rw [e]
    have hb1 : A.valuation (algebraMap F Ω b * δ) < 1 := by
      by_cases hb : b = 0
      · rw [hb, map_zero, zero_mul, Valuation.map_zero]; exact zero_lt_one
      have hne1 := KL b hb
      have hne : A.valuation (algebraMap F Ω a) ≠ A.valuation (algebraMap F Ω b * δ) := by
        intro heq
        have hbd : algebraMap F Ω b * δ ≠ 0 := mul_ne_zero ((_root_.map_ne_zero _).2 hb) hδ0
        have ha : a ≠ 0 := by
          rintro rfl
          rw [map_zero, Valuation.map_zero] at heq
          exact hbd ((Valuation.zero_iff _).1 heq.symm)
        apply KL (b / a) (div_ne_zero hb ha)
        have haw : A.valuation (algebraMap F Ω a) ≠ 0 :=
          (Valuation.ne_zero_iff _).2 ((_root_.map_ne_zero _).2 ha)
        rw [map_div₀, div_mul_eq_mul_div, map_div₀, ← heq, div_self haw]
      rw [Valuation.map_add_of_distinct_val _ hne] at hx
      exact lt_of_le_of_ne (le_trans (le_max_right _ _) hx) hne1
    rw [map_mul]
    have h2 : A.valuation (-2 : Ω) ≤ 1 := by
      rw [Valuation.map_neg]
      have := valuation_natCast_le_one A 2
      simpa using this
    calc A.valuation (-2 : Ω) * A.valuation (algebraMap F Ω b * δ)
        ≤ 1 * A.valuation (algebraMap F Ω b * δ) := by gcongr
      _ < 1 := by rw [one_mul]; exact hb1
  obtain ⟨σ, hσ, hστ⟩ := GlobalTheory.InertiaLift.exists_mem_Ine_lift A M τ hcond
  refine ⟨σ, hσ, ?_⟩
  have h1 := hστ ⟨δ, hδM⟩
  rw [AlgEquiv.restrictNormal_commutes] at h1
  change σ δ = σ₀ δ at h1
  rw [h1, hσ₀']
  intro h
  have h2 : (2 : Ω) * δ = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact two_ne_zero h3
  · exact hδ0 h3

end GlobalTheory.SqrtNegRam
