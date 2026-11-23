import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def QuotSectionsFinite.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle k x) (J : Ideal (Poly k N)),
    Module.Finite k (SubSystem.quotH Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
