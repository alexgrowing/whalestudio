import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightAssemblyFull
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegreeRatio
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitLocalSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterZero
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitConjSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem HeightAsIntersection.of_chart_and_centre (hR : OrbitChartRing.Statement) (hM : OrbitChartMax.Statement)
    (hF : OrbitChartResidue.Statement) (hU : OrbitChartMult.Statement)
    (hP : LocalLengthPlaces.Statement) (hC : OrbitCenterChart.Statement)
    (hS : PlaceCentredSum.Statement) (hT : OrbitChartTerm.Statement)
    (hLe : OrbitCenterLe.Statement) (hIff : OrbitCenterMemIff.Statement)
    (hDiv : OrbitCenterDivSupp.Statement) : HeightAsIntersection.Statement :=
  HeightAsIntersection.of_orbit_parts OrbitDegreeRatio.proof
    (OrbitLocalSum.proof hR hM hF hU hP hC hS hT) (OrbitCenterZero.proof hLe hIff hDiv)
    OrbitConjSum.proof

end GroundTheory.Heights₂.Heights
