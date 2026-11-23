import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

def CMHeightAddDim.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (J : Ideal B), J ≠ ⊤ →
    (J.height : WithBot ℕ∞) + ringKrullDim (B ⧸ J) = ringKrullDim B

end GroundTheory.Heights₂.Heights
