import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.KaehlerPlace
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedFibresAlmostAllOfSeparableDedekindCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherNormalizationFiniteAevalPowAddStatement
open Polynomial

namespace GlobalTheory
open GroundTheory.FunctionField GroundTheory.Arith.SchemeCoh KaehlerDifferential

theorem ringKrullDim_eq_one_of_isDedekindDomain_of_not_isField (A : Type) [CommRing A] [IsDedekindDomain A] (h : ¬ IsField A) : ringKrullDim A = 1 := by
  have hle : ringKrullDim A ≤ 1 := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 A)
  have h0 : ringKrullDim A ≠ 0 := fun h0 => h (by
      have : Ring.KrullDimLE 0 A := by
        rw [Ring.krullDimLE_iff, h0]
        rfl
      exact Ring.KrullDimLE.isField_of_isDomain)
  have hnn : 0 ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim A = d at hle h0 hnn ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe n =>
    have h1 : n ≤ 1 := by exact_mod_cast hle
    have h2 : n ≠ 0 := by exact_mod_cast h0
    rw [le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h2)]
    rfl

theorem exists_aeval_finite_of_ringKrullDim_eq_one : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A],
    ringKrullDim A = 1 → ∃ t : A, (Polynomial.aeval (R := k) t).Finite := by
  intro k A _ _ _ _ _ hdim
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hs : ringKrullDim A = s := by
    let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
    have _ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x => hfin.to_isIntegral x⟩
    have _ : FaithfulSMul (MvPolynomial (Fin s) k) A :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 hg
    rw [GlobalTheory.ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) A,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hs1 : s = 1 := by
    rw [hdim] at hs
    exact_mod_cast hs.symm
  subst hs1
  refine ⟨g (MvPolynomial.X 0), ?_⟩
  let e : k[X] →ₐ[k] MvPolynomial (Fin 1) k := Polynomial.aeval (MvPolynomial.X 0)
  have he : Function.Surjective e := by
    rw [← AlgHom.range_eq_top]
    change (Polynomial.aeval (R := k) (MvPolynomial.X (R := k) (0 : Fin 1))).range = ⊤
    rw [← Algebra.adjoin_singleton_eq_range_aeval, ← MvPolynomial.adjoin_range_X, Set.range_unique]
    rfl
  have hcomp : Polynomial.aeval (R := k) (g (MvPolynomial.X 0)) = g.comp e := by
    apply Polynomial.algHom_ext
    simp [e]
  rw [hcomp]
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ he)

theorem aeval_injective_of_finite_of_not_isField : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (y : A),
    (Polynomial.aeval (R := k) y).Finite → ¬ IsField A → Function.Injective (Polynomial.aeval (R := k) y) := by
  intro k A _ _ _ _ y hy hA
  rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨p, hp, hp0⟩ := hne
  have hyi : IsIntegral k y := (show IsAlgebraic k y from ⟨p, hp0, hp⟩).isIntegral
  set B : Subalgebra k A := (Polynomial.aeval (R := k) y).range with hB
  haveI : Algebra.IsIntegral k B := by
    constructor
    rintro ⟨z, q, rfl⟩
    have : IsIntegral k (Polynomial.aeval y q) := by
      rw [Polynomial.aeval_eq_sum_range]
      refine IsIntegral.sum _ fun i _ => ?_
      exact (hyi.pow i).smul _
    exact (isIntegral_algHom_iff B.val Subtype.val_injective).1 this
  haveI : Algebra.IsIntegral k A := by
    constructor
    intro x
    have hx : (Polynomial.aeval (R := k) y).toRingHom.IsIntegralElem x := hy.to_isIntegral x
    obtain ⟨f, hfm, hf⟩ := hx
    let φ : k[X] →+* B := (Polynomial.aeval (R := k) y).rangeRestrict.toRingHom
    have hxB : IsIntegral B x := by
      refine ⟨f.map φ, hfm.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      have e : (algebraMap B A).comp φ = (Polynomial.aeval (R := k) y).toRingHom := RingHom.ext fun q => rfl
      rw [e]
      exact hf
    exact isIntegral_trans x hxB
  exact hA ((Algebra.IsIntegral.isField_iff_isField (algebraMap k A).injective).1 (Field.toIsField k))

theorem exists_D_algebraMap_fractionRing_ne_zero : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [IsFunctionField k (FractionRing A)],
    ∃ a : A, D k (FractionRing A) (algebraMap A (FractionRing A) a) ≠ 0 := by
  intro k A _ _ _ _ _
  have hnt := kaehlerDifferential_nontrivial (k := k) (K := FractionRing A)
  by_contra h
  push_neg at h
  have hall : ∀ x : FractionRing A, D k (FractionRing A) x = 0 := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, h a, h b]
    simp
  have htop : (⊤ : Submodule (FractionRing A) Ω[FractionRing A⁄k]) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨x, rfl⟩
    exact hall x
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[FractionRing A⁄k])
  have hmem : ω ∈ (⊥ : Submodule (FractionRing A) Ω[FractionRing A⁄k]) := htop ▸ Submodule.mem_top
  exact hω ((Submodule.mem_bot _).1 hmem)

theorem isFunctionField_fractionRing_of_ringKrullDim_eq_one (k A : Type) [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (hR : ringKrullDim A = 1) :
    IsFunctionField k (FractionRing A) := by
  have htrA : Algebra.trdeg k A = 1 := by
    obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
    have hs := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_of_normalization k g hg hfin.to_isIntegral
    rw [hR] at hs
    have hs1 : s = 1 := by exact_mod_cast hs.symm
    subst hs1
    rw [GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_normalization k g hg hfin.to_isIntegral]
    simp
  have htr : Algebra.trdeg k (FractionRing A) = 1 := by
    have : FaithfulSMul A (FractionRing A) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A _)
    have : Algebra.IsAlgebraic A (FractionRing A) :=
      IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
    rw [← trdeg_add_eq k A (A := FractionRing A), htrA, trdeg_eq_zero (R := A) (A := FractionRing A),
      add_zero]
  have : Algebra.Transcendental k (FractionRing A) := by
    rw [← trdeg_ne_zero_iff, htr]
    exact one_ne_zero
  obtain ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := k) (A := FractionRing A)
  refine ⟨x, hx, ?_⟩
  have hbx : IsTranscendenceBasis k ((↑) : ({x} : Set (FractionRing A)) → FractionRing A) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set (FractionRing A)))).2 hx)
      (by rw [htr, Cardinal.mk_singleton])
  have halg := hbx.isAlgebraic_field
  rw [Subtype.range_coe] at halg
  have : Algebra.EssFiniteType A (FractionRing A) :=
    Algebra.EssFiniteType.of_isLocalization (FractionRing A) (nonZeroDivisors A)
  have : Algebra.EssFiniteType k (FractionRing A) := Algebra.EssFiniteType.comp k A (FractionRing A)
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {x}) (FractionRing A) :=
    Algebra.EssFiniteType.of_comp k _ (FractionRing A)
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem exists_separable_normalisation_reduced_fibres : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A], ¬ IsField A → ∃ y : A, (Polynomial.aeval (R := k) y).Finite ∧ ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → y - algebraMap k A α ∉ Q ^ 2 := by
  intro k A _ _ _ _ _ _ hA
  have hdim : ringKrullDim A = 1 := ringKrullDim_eq_one_of_isDedekindDomain_of_not_isField A hA
  haveI : IsFunctionField k (FractionRing A) :=
    isFunctionField_fractionRing_of_ringKrullDim_eq_one k A hdim
  obtain ⟨t, ht⟩ := exists_aeval_finite_of_ringKrullDim_eq_one k A hdim
  obtain ⟨a, ha⟩ := exists_D_algebraMap_fractionRing_ne_zero k A
  have key : ∃ y : A, (Polynomial.aeval (R := k) y).Finite ∧
      D k (FractionRing A) (algebraMap A (FractionRing A) y) ≠ 0 := by
    by_cases hD : D k (FractionRing A) (algebraMap A (FractionRing A) t) = 0
    · obtain ⟨M, hM⟩ := GlobalTheory.T.noether_normalization_finite_aeval_pow_add k A t a ht
      refine ⟨t ^ M + a, hM, ?_⟩
      rw [map_add, map_pow, map_add, Derivation.leibniz_pow, hD, smul_zero, smul_zero, zero_add]
      exact ha
    · exact ⟨t, ht, hD⟩
  obtain ⟨y, hy, hDy⟩ := key
  haveI := isSeparable_of_D_ne_zero hDy
  exact ⟨y, hy, GlobalTheory.T.reduced_fibres_almost_all_of_separable_dedekind_curve k A y hy (aeval_injective_of_finite_of_not_isField k A y hy hA) this⟩

end GlobalTheory
