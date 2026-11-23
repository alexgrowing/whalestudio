import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecondVeronese
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Topology

noncomputable section

theorem leviForm_comp_clm {J : Type*} [Fintype J] (φ : (J → ℂ) → ℝ) (L : (J → ℂ) →L[ℝ] (J → ℂ))
    (hL : ∀ w, L (Complex.I • w) = Complex.I • L w) (z : J → ℂ)
    (hφ : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ φ (L y))
    (hφ2 : DifferentiableAt ℝ (fderiv ℝ φ) (L z)) (w : J → ℂ) :
    leviForm (φ ∘ L) z w = leviForm φ (L z) (L w) := by
  set R := (ContinuousLinearMap.compL ℝ (J → ℂ) (J → ℂ) ℝ).flip L with hR
  have hev : fderiv ℝ (φ ∘ L) =ᶠ[𝓝 z] fun y => R (fderiv ℝ φ (L y)) := by
    filter_upwards [hφ] with y hy
    rw [fderiv_comp y hy L.differentiableAt, L.fderiv]
    rfl
  have hd : HasFDerivAt (fun y => R (fderiv ℝ φ (L y))) (R.comp ((fderiv ℝ (fderiv ℝ φ) (L z)).comp L)) z :=
    R.hasFDerivAt.comp z (hφ2.hasFDerivAt.comp z L.hasFDerivAt)
  have key : ∀ v, fderiv ℝ (fderiv ℝ (φ ∘ L)) z v v = fderiv ℝ (fderiv ℝ φ) (L z) (L v) (L v) := by
    intro v
    rw [hev.fderiv_eq, hd.fderiv]
    rfl
  unfold leviForm
  rw [key, key, hL]

theorem contDiffAt_log_fs {J : Type} [Fintype J] {y : J → ℂ} (hy : y ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Real.log ((fsMetric J).ρ y)) y :=
  ((ProjLine.isSmoothMetric_fs (J := J) y hy).contDiffAt (isOpen_ne.mem_nhds hy)).log
    ((fsMetric J).pos y hy).ne'

namespace Veronese

def scaleLin (D : ℕ) : (Ix (Idx D) → ℂ) →ₗ[ℂ] (Ix (Idx D) → ℂ) where
  toFun := scale D
  map_add' z z' := by
    funext q
    simp only [scale, Pi.add_apply]
    ring
  map_smul' c z := by
    funext q
    simp only [scale, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def scaleL (D : ℕ) : (Ix (Idx D) → ℂ) →L[ℝ] (Ix (Idx D) → ℂ) :=
  (LinearMap.toContinuousLinearMap (scaleLin D)).restrictScalars ℝ

theorem scaleL_I (D : ℕ) (w : Ix (Idx D) → ℂ) : scaleL D (Complex.I • w) = Complex.I • scaleL D w :=
  (scaleLin D).map_smul Complex.I w

end Veronese

open Veronese

theorem VeroneseSemipos.proof : VeroneseSemipos.Statement := by
  intro D
  refine ⟨(isSmoothMetric_metric D).mono fun z hz h0 => ?_, fun z hz w _ => ?_⟩
  · obtain ⟨i, hi⟩ := hz ()
    exact hi (congrFun h0 _)
  · have hz0 : z ≠ 0 := by
      intro h0
      obtain ⟨i, hi⟩ := hz.1 ()
      exact hi (congrFun h0 _)
    have e : (fun z => Real.log ((HermLine.ofCone (metric D)).h z)) =
        (fun y => Real.log ((fsMetric (Ix (Idx D))).ρ y)) ∘ scaleL D := rfl
    have hφ : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ (fun y => Real.log ((fsMetric (Ix (Idx D))).ρ y)) (scaleL D y) := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
      exact (contDiffAt_log_fs (scale_ne_zero hy)).differentiableAt (by simp)
    have hφ2 : DifferentiableAt ℝ (fderiv ℝ fun y => Real.log ((fsMetric (Ix (Idx D))).ρ y)) (scaleL D z) :=
      ((contDiffAt_log_fs (scale_ne_zero hz0)).fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt
        one_ne_zero
    rw [e, leviForm_comp_clm _ _ (scaleL_I D) z hφ hφ2 w]
    exact ProjLine.leviForm_log_fs_nonneg (scale_ne_zero hz0) (scaleL D w)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
