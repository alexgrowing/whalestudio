import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleimanLow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedKleimanTop.Statement : Prop :=
  ∀ d : ℕ, 2 ≤ d → MixedKleiman.AtDim (d - 1) → MixedKleiman.LowAt d → MixedKleiman.TopAt d

end GroundTheory.Heights₂.Heights.HilbertSamuel
