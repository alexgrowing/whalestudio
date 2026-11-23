import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogNormGradDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ContDiff

noncomputable section

namespace LogNormGradDensNonneg

theorem log_fs_eq_std (n : ℕ) :
    (fun z : Fin n → ℂ => Real.log ((ReciprocityTheory.ChartRestriction.G.Geo.fsMetric (Fin n)).ρ z)) =
      fun z => Real.log ((HermNorm.std n).dualNorm z) := by
  funext z
  simp [ReciprocityTheory.ChartRestriction.G.Geo.fsMetric, HermNorm.dualNorm, HermNorm.std, EuclideanSpace.norm_eq]

theorem levi_log_dualNorm_nonneg {n : ℕ} (h : HermNorm n) {x : Fin n → ℂ} (hx : x ≠ 0)
    (w : Fin n → ℂ) : 0 ≤ levi (fun x => Real.log (h.dualNorm x)) x w := by
  set T : (Fin n → ℂ) → Fin n → ℂ := fun x => (h.matᵀ)⁻¹ *ᵥ x with hT
  set F : (Fin n → ℂ) → ℝ := fun z => Real.log ((ReciprocityTheory.ChartRestriction.G.Geo.fsMetric (Fin n)).ρ z) with hF
  have hTx : T x ≠ 0 := by
    intro h0
    have : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact h.isUnit_det),
        Matrix.one_mulVec]
    exact hx (by rw [← this]; simp only [hT] at h0; rw [h0, Matrix.mulVec_zero])
  have hcomp : (fun x => Real.log (h.dualNorm x)) = F ∘ T := by
    funext z
    simp [hF, hT, ReciprocityTheory.ChartRestriction.G.Geo.fsMetric, HermNorm.dualNorm, EuclideanSpace.norm_eq]
  have hTa : AnalyticAt ℂ T x := by
    have := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h.matᵀ)⁻¹)).analyticAt x
    simp only [LinearMap.coe_toContinuousLinearMap'] at this
    convert this using 1
    funext z
    rw [Matrix.mulVecLin_apply]
  have hFc : ContDiffAt ℝ 2 F (T x) := by
    rw [hF, log_fs_eq_std]
    exact (((contDiffOn_log_dualNorm (HermNorm.std n)).contDiffAt
      (isOpen_compl_singleton.mem_nhds hTx)).of_le (WithTop.coe_le_coe.mpr le_top))
  rw [hcomp, levi_comp w hTa hFc]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hTx _

end LogNormGradDensNonneg

theorem LogNormGradDensNonneg.proof : LogNormGradDensNonneg.Statement := by
  intro n e h s y v hs hsy
  set t : (Fin n → ℂ) → ℝ := fun x => Real.log (h.dualNorm x) with ht
  set V : Set (Fin (e + 1) → ℂ) := {z | AnalyticAt ℂ s z ∧ s z ≠ 0} with hVdef
  have hV : IsOpen V := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    filter_upwards [hz.1.eventually_analyticAt,
      hz.1.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hz.2)] with u hu hu'
    exact ⟨hu, hu'⟩
  have htc : ∀ x : Fin n → ℂ, x ≠ 0 → ContDiffAt ℝ 2 t x := fun x hx =>
    ((contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds hx)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hC : ∀ z ∈ V, ContDiffAt ℝ 2 (t ∘ s) z := fun z hz =>
    (htc (s z) hz.2).comp z (hz.1.restrictScalars (𝕜 := ℝ)).contDiffAt
  refine gradDensNonneg_thm e (fun _ => t ∘ s) v V hV
    (fun _ => fun z hz => (hC z hz).contDiffWithinAt) ?_ y ⟨hs, hsy⟩
  intro _ z hz ξ
  rw [levi_comp ξ hz.1 (htc (s z) hz.2)]
  exact LogNormGradDensNonneg.levi_log_dualNorm_nonneg h hz.2 _

end

end GroundTheory.Heights₂.Heights
