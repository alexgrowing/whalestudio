import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiAnalyticNormality
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolGermsIntegrallyClosed.Statement : Prop :=
  ∀ (d : ℕ) (y : Fin d → ℂ), IsDomain (holGerms y) ∧ IsIntegrallyClosed (holGerms y)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
