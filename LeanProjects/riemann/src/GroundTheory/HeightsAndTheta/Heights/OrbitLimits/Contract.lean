import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.Intersections.MixedDiscEqZeroOfMulVec
import GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
import GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.Inter

theorem Contract.pulledBackForms_topDensity_vanish : pointForm_holds.Statement :=
  pointForm_holds.proof (pointFormRank_holds.proof RatioAlgDep.proof) pointFormEuler_holds.proof

theorem Contract.of_found (hIm : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageArithStatement)
    (hV : GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.ContractStatement :=
  contract_of hIm Contract.pulledBackForms_topDensity_vanish hV

end GroundTheory.Heights₂.Heights.Targets
