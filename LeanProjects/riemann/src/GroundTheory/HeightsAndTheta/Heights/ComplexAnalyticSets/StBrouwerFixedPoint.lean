import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def BrouwerFixedPoint.Statement : Prop :=
  ∀ (n : ℕ) (f : (Fin n → ℝ) → Fin n → ℝ),
    ContinuousOn f (Metric.closedBall 0 1) →
      Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1) →
        ∃ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, f x = x

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
