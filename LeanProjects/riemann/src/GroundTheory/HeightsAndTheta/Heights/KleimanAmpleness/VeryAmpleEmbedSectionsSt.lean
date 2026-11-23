import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def VeryAmpleEmbed.Sections.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω)
    (Q : LineBundle k y) (r : ℕ) (h : Fin (r + 1) → Ω), y ≠ 0 → IsVeryAmpleBy Q.toSubSystem h →
    ∀ m : ℕ, (Q.toSubSystem.pow m).secs = (twistSys k h (m : ℤ)).secs

end

end GroundTheory.Heights₂.Heights.Kleiman
