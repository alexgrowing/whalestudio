import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def DegreeSupInf.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (F G : Submodule (𝓞 K) E.carrier),
    E.degree F + E.degree G ≤ E.degree (F ⊔ G) + E.degree (F ⊓ G)

end GroundTheory.Heights₂.Heights
