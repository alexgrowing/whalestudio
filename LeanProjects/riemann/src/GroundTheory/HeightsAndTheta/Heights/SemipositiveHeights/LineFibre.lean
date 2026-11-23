import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLinearQuotient
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHomogeneousOfIsMultiHomogOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

theorem LineFibre.full : ReciprocityTheory.ChartRestriction.G.AI.I4.LineFibreStatement := by
  intro F _ ι₀ _ Q J hQ hS hJ m
  exact GroundTheory.Heights₂.Heights.Inter.LineFibreBlocks.proof GroundTheory.Heights₂.Heights.Inter.LinearQuotient.proof
    F Unit (fun _ => ι₀) () Q J (fun _ => rfl) hQ hS hJ (fun _ => m)

end GroundTheory.Heights₂.Heights.ForSecondHalf
