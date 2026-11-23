import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjDegGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRankOfSections
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertPrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertDimZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertIncrement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntersectionRecursion
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulesFromPrimes
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedFiltration
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiltrationHilbSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

open GroundTheory.Heights₂.Heights.HilbertSamuel

theorem HilbertPrime.closed : HilbertPrime.Statement.{0} :=
  HilbertPrime.proof HilbertDimZero.proof (HilbertIncrement.proof IntersectionRecursion.proof)
    (MixedNumberPolynomial.proof (MultigradedHilbertPolynomial.proof EventualPolynomial.proof))
    (ModulesFromPrimes.proof MultigradedFiltration.proof FiltrationHilbSum.proof DegLTGrowth.proof)

theorem RankOfSections.closed : RankOfSections.Statement :=
  RankOfSections.proof HilbertPrime.closed
    (MixedNumberPolynomial.proof (MultigradedHilbertPolynomial.proof EventualPolynomial.proof))

theorem ProjDegGenDeg.proof : ProjDegGenDeg.Statement :=
  HilbertSamuel.ProjDegGenDeg.proof RankOfSections.closed

end GroundTheory.Heights₂.Heights.Swarm
