import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights (localMult)

def LocalMultComap.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (σ : R →+* S) (I W : Ideal S),
    Function.Surjective σ → W.IsPrime → localMult (I.comap σ) (W.comap σ) = localMult I W

end GroundTheory.Heights₂.Heights.Targets
