import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def CompletionNormalDescent.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (J : Ideal R), IsNoetherianRing R → J ≤ (⊥ : Ideal R).jacobson →
    IsDomain (AdicCompletion J R) → IsIntegrallyClosed (AdicCompletion J R) →
      IsDomain R ∧ IsIntegrallyClosed R

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
