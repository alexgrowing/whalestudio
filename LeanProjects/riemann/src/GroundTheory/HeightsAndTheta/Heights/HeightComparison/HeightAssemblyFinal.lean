import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightAssemblyClosed
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartRing
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMax
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartQuot
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartDehom
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMult
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCard
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredPlacesFinite
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredRingNormal
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalNormalIndex
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCentred
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlacesRingQuot
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalLengthPlaces
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterChart
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlaceCentredSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartTerm
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterLe
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterMemIff
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterPrime
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PSubringPrimeMaximal
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem HeightAsIntersection.full : HeightAsIntersection.Statement :=
  have hM : OrbitChartMax.Statement := OrbitChartMax.proof
  have hQ : OrbitChartQuot.Statement := OrbitChartQuot.proof
  have hIff : OrbitCenterMemIff.Statement := OrbitCenterMemIff.proof
  HeightAsIntersection.of_chart_and_centre OrbitChartRing.proof hM
    (OrbitChartResidue.proof hM hQ (OrbitChartDehom.proof hM hQ))
    OrbitChartMult.proof
    (LocalLengthPlaces.proof LocalQuotCard.proof CentredPlacesFinite.proof
      (LocalQuotCentred.proof CentredRingNormal.proof LocalNormalIndex.proof) PlacesRingQuot.proof)
    OrbitCenterChart.proof PlaceCentredSum.proof OrbitChartTerm.proof OrbitCenterLe.proof hIff
    (OrbitCenterDivSupp.proof hIff (OrbitCenterPrime.proof hIff) SubringPrimeMaximal.proof)

end GroundTheory.Heights₂.Heights
