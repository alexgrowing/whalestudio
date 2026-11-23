import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreCriterion.Statement : Prop :=
  ∀ (A : Type) [CommRing A], IsNoetherianRing A → (NormalRing A ↔ SerreR A 1 ∧ SerreS A 2)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
