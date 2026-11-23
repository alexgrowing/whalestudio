import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory

noncomputable section

def SphereLongitudeCoordinates.Statement : Prop :=
  sphereMeasure.map (fun n : Sphere2 => (n : E3)) =
    (ENNReal.ofReal (4 * Real.pi))⁻¹ •
      (volume.restrict (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ioc 0 (2 * Real.pi))).map
        (fun p : ℝ × ℝ => spherePoint p.1 p.2)

end

end GroundTheory.Heights₂.Heights.FlagBundles
