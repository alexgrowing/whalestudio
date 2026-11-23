import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.QuadraticFieldSqrtNegSeven
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane

def realEisenstein (τ : ℍ) (s : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)

theorem realEisenstein_nonneg (τ : ℍ) (s : ℝ) : 0 ≤ realEisenstein τ s := by
  refine tsum_nonneg fun p => ?_
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg τ.im_pos.le _) (Real.rpow_nonneg (norm_nonneg _) _)

end GroundTheory.Heights₂.Theta
