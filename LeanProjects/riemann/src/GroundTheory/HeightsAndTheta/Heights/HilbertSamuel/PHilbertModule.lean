import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

universe u v

theorem HilbertModule.proof (hMP : ModulesFromPrimes.Statement.{u, v})
    (hHP : HilbertPrime.Statement.{u}) : HilbertModule.Statement.{u, v} :=
  fun d => hMP d fun e _ => hHP e

end GroundTheory.Heights₂.Heights.HilbertSamuel
