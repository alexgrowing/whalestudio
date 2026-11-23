import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotBotOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem graphOver_eq {k m : ℕ} (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (A : Set (EuclideanSpace ℝ (Fin k))) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.graphOver F A =
      GroundTheory.Heights₂.Heights.realGraphPt F '' A :=
  rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
