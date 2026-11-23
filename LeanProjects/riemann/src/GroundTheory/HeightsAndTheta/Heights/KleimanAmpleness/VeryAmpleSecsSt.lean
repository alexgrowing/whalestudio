import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def VeryAmpleSecs.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy Nb.toSubSystem h →
    ∀ n : ℕ, (Nb.toSubSystem.pow n).secs = ((twistSys k h 1).pow n).secs

end

end GroundTheory.Heights₂.Heights.Kleiman
