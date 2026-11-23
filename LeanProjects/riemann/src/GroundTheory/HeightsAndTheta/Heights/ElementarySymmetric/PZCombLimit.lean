import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem ZCombLimit.proof : GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombLimit.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombLimit.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedHilbertPolynomial.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial.proof))

end GroundTheory.Heights₂.Heights.Swarm
