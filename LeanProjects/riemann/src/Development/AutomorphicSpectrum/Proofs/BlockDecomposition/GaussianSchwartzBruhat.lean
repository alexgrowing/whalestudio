import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RankinSelberg

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Classical SchwartzMap

noncomputable section

theorem isEmpty_complexPlaces_rat : IsEmpty {w : InfinitePlace ℚ // IsComplex w} := by
  refine ⟨fun w => ?_⟩
  exact (not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2

theorem norm_sq_mixedToEuclidean_rat (x : mixedSpace ℚ) :
    ‖GroundTheory.Global.mixedToEuclidean ℚ x‖ ^ 2 = ∑ w, x.1 w ^ 2 := by
  haveI := isEmpty_complexPlaces_rat
  rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
  have h2 : ‖(GroundTheory.Global.mixedToEuclidean ℚ x).snd‖ = 0 := by
    rw [EuclideanSpace.norm_eq]
    simp
  rw [h2]
  have h1 : ∀ w, (GroundTheory.Global.mixedToEuclidean ℚ x).fst.ofLp w = x.1 w := fun _ => rfl
  simp only [h1, Real.norm_eq_abs, sq_abs]
  simp

theorem gaussian_exists : Ad3.R.GS := by
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (GroundTheory.Automorphic.Adele2.toEuclid2 ℚ)
    (GroundTheory.Global.gaussianSchwartz _), fun y => ?_⟩
  have h : ‖GroundTheory.Automorphic.Adele2.toEuclid2 ℚ y‖ ^ 2 = ∑ i, ∑ w, (y i).1 w ^ 2 := by
    rw [GroundTheory.Automorphic.Adele2.toEuclid2_apply, WithLp.prod_norm_sq_eq_of_L2, Fin.sum_univ_two]
    exact congrArg₂ (· + ·) (norm_sq_mixedToEuclidean_rat _) (norm_sq_mixedToEuclidean_rat _)
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, h]

end

end GlobalTheory.CompanionTheory.RankinSelberg
