import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def VeryAmpleEmbed.Numbers.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω)
    (Q : LineBundle k y) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy Q.toSubSystem h →
    ∀ n : ℕ, IsSubvar y (primeOf (S := k) y) n →
      IsSubvar h (primeOf (S := k) h) n ∧
        interNum (primeOf (S := k) y) (fun _ : Fin n => Q.toSubSystem) =
          interNum (primeOf (S := k) h) (fun _ : Fin n => twistSys k h 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
