import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneDim
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 vecAt awayIntegral awayBox)
open GroundTheory.Automorphic.GJMatrix (cosetInd localTensor localFourierPi localMeasurePi)
open Ad3 Ad3.R
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap nonZeroDivisors Classical

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RSFT.GaussPlane

section Helpers

open NumberField.mixedEmbedding
open scoped FourierTransform RealInnerProductSpace

instance isEmpty_complexPlaces : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
  ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr w.2 (by
    rw [Subsingleton.elim w.1 Rat.infinitePlace]; exact Rat.isReal_infinitePlace)⟩

theorem norm_mixedToEuclidean_sq_rat (x : mixedSpace ℚ) :
    ‖mixedToEuclidean ℚ x‖ ^ 2 = ∑ w, x.1 w ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change ⟪(euclidean.toMixed ℚ).symm (mapComplexCoord ℚ sqrtTwoSMulComplex x),
    (euclidean.toMixed ℚ).symm (mapComplexCoord ℚ sqrtTwoSMulComplex x)⟫ = _
  rw [inner_toMixed_symm, mapComplexCoord_apply]
  simp [sq]

theorem norm_mixedToEuclideanConj_sq_rat (x : mixedSpace ℚ) :
    ‖mixedToEuclideanConj ℚ x‖ ^ 2 = ∑ w, x.1 w ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change ⟪(euclidean.toMixed ℚ).symm (mapComplexCoord ℚ sqrtTwoSMulConj x),
    (euclidean.toMixed ℚ).symm (mapComplexCoord ℚ sqrtTwoSMulConj x)⟫ = _
  rw [inner_toMixed_symm, mapComplexCoord_apply]
  simp [sq]

theorem norm_toEuclid2_sq_rat (x : Fin 2 → mixedSpace ℚ) :
    ‖Adele2.toEuclid2 ℚ x‖ ^ 2 = ∑ i, ∑ w, (x i).1 w ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, Adele2.toEuclid2_apply, WithLp.prod_inner_apply,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, Fin.sum_univ_two,
    norm_mixedToEuclidean_sq_rat, norm_mixedToEuclidean_sq_rat]

theorem norm_toEuclid2Conj_sq_rat (x : Fin 2 → mixedSpace ℚ) :
    ‖Adele2.toEuclid2Conj ℚ x‖ ^ 2 = ∑ i, ∑ w, (x i).1 w ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, Adele2.toEuclid2Conj_apply, WithLp.prod_inner_apply,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, Fin.sum_univ_two,
    norm_mixedToEuclideanConj_sq_rat, norm_mixedToEuclideanConj_sq_rat]

theorem mixedFourier2_gauss (γ : 𝓢(Fin 2 → mixedSpace ℚ, ℂ)) (hγ : IsGauss γ)
    (y : Fin 2 → mixedSpace ℚ) : Adele2.mixedFourier2 ℚ γ y = γ y := by
  have hcomp : (γ : (Fin 2 → mixedSpace ℚ) → ℂ) ∘ (Adele2.toEuclid2 ℚ).symm =
      fun v => Complex.exp (-(Real.pi : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v
    have hv : ‖v‖ ^ 2 = ∑ i, ∑ w, (((Adele2.toEuclid2 ℚ).symm v) i).1 w ^ 2 := by
      rw [← norm_toEuclid2_sq_rat, ContinuousLinearEquiv.apply_symm_apply]
    rw [Function.comp_apply, hγ, ← hv]
    push_cast
    rfl
  have hb : 0 < ((Real.pi : ℂ)).re := by simpa using Real.pi_pos
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Adele2.mixedFourier2_eq, hcomp, fourier_gaussian_innerProductSpace hb, hγ,
    ← norm_toEuclid2Conj_sq_rat, div_self hpi, Complex.one_cpow, one_mul]
  push_cast
  congr 1
  field_simp

end Helpers

theorem mixedFourier2_gauss_rot : ∀ (γ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)), IsGauss γ → ∀ r : Fin 2 → 𝔸[ℚ], Adele2.mixedFourier2 ℚ γ (Adele2.infPart ![r 1, -r 0]) = γ (Adele2.infPart r) := by
  intro γ hγ r
  rw [show Adele2.mixedFourier2 ℚ γ (Adele2.infPart ![r 1, -r 0]) =
    γ (Adele2.infPart ![r 1, -r 0]) from mixedFourier2_gauss γ hγ _, hγ, hγ]
  have h1 : Adele2.infPart ![r 1, -r 0] 0 = Adele2.infPart r 1 := rfl
  have h2 : Adele2.infPart ![r 1, -r 0] 1 = -Adele2.infPart r 0 :=
    congrFun (Adele2.infPart_neg r) 0
  simp only [Fin.sum_univ_two, h1, h2, Prod.fst_neg, Pi.neg_apply, neg_sq]
  rw [add_comm]

end GlobalTheory.CompanionTheory.RSFT.GaussPlane
