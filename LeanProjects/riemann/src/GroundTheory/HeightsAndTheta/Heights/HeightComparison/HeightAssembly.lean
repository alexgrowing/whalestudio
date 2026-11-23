import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Height
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegree
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem HeightAsIntersection.of_parts (hV : OrbitDivVertical.Statement)
    (hF : OrbitFiniteSum.Statement) (hA : OrbitArchSum.Statement) :
    HeightAsIntersection.Statement :=
  HeightAsIntersection.proof OrbitCurve.full OrbitDegree.full (HeightRecR.proof hV hF hA)

end GroundTheory.Heights₂.Heights
