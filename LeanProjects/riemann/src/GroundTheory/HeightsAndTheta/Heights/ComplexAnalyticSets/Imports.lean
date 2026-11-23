import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreNormalOfRegularDepth.Statement : Prop :=
  ∀ (A : Type) [CommRing A], IsNoetherianRing A → SerreR A 1 → SerreS A 2 → NormalRing A

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
