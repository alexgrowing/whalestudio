import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem covDet (n : ℕ) (f' : V n →L[ℂ] V n) :
    |(f'.restrictScalars ℝ : V n →L[ℝ] V n).det| =
      ‖LinearMap.det (f' : V n →ₗ[ℂ] V n)‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]

theorem cov (n : ℕ) : CovStatement n := by
  intro W G f hW hG hinj _
  have hd : ∀ y ∈ W, HasFDerivWithinAt G ((fderiv ℂ G y).restrictScalars ℝ) W y := fun y hy =>
    (((hG y hy).differentiableAt (hW.mem_nhds hy)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hW.measurableSet hd hinj f]
  simp only [covDet]

end ReciprocityTheory.L2DbarEstimates.I
