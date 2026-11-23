import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def VeryAmpleDegree.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsSubvar x (primeOf (S := k) x) e →
    IsVeryAmpleBy Nb.toSubSystem h →
    interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) =
      interNum (primeOf (S := k) h) (fun _ : Fin e => twistSys k h 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
