import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedMixedNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedProductNonneg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

theorem GeneratedMixedNonneg.proof (hGP : GeneratedProductNonneg.Statement) :
    GeneratedMixedNonneg.Statement := by
  intro F _ K _ _ ι _ _ V n bs hV hgen
  exact hGP F K ι (fun V _ L => NumbersDVR.intNum F V L) V n bs
    (NumbersDVR.IntNumIsFieldIntersection.full F K ι) hV hgen

end GroundTheory.Heights₂.Heights.HilbertSamuel
