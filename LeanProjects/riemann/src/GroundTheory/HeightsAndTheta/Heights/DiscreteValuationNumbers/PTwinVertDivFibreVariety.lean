import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreMore
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivSupportFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalDivisorFibreVariety.proof : VerticalDivisorFibreVariety.Statement := by
  intro O _ _ _ K _ ι _ P d hP b f g hV W hW
  exact VerticalDivisorSupportFibre.proof O K ι P d hP b f g hV W (Finsupp.mem_support_iff.mp hW)

end GroundTheory.Heights₂.Heights.NumbersDVR
