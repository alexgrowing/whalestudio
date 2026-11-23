import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EisensteinTails.Statements
import GroundTheory.HeightsAndTheta.Heights.EisensteinTails.ExistsIntOfIsIntegralThree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LeavesOrthogonalSum

open Complex

theorem rowSum_eq (m : ℤ) (τ : UpperHalfPlane) (s : ℂ) :
    rowSum m τ s = GroundTheory.Heights₂.Heights.LeavesOrthogonalSum.rowSum m τ s := rfl

theorem freqIntegral_eq (k : ℤ) (Y : ℝ) (s : ℂ) :
    freqIntegral k Y s = GroundTheory.Heights₂.Heights.LeavesOrthogonalSum.freqIntegral k Y s := by
  rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LeavesOrthogonalSum
