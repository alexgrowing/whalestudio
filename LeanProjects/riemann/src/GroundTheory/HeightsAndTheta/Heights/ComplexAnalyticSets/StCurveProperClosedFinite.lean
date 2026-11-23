import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def CurveProperClosedFinite.Statement : Prop :=
  ∀ (n : ℕ) (W K : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1 → ¬ K ≤ W →
      (zeroSet W ∩ zeroSet K).Finite

end

end GroundTheory.Heights₂.Heights
