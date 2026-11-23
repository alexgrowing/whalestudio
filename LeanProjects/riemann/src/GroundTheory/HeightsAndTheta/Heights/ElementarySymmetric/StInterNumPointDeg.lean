import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def InterNumPointDeg.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), IsSubvar x pp 0 →
      interNum pp (![] : Fin 0 → SubSystem k x Ω) =
        (FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
