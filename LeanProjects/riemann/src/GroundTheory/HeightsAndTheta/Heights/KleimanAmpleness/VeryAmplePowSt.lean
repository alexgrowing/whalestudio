import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def VeryAmplePow.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (H : LineBundle S x) (j : ℕ), IsVeryAmple H.toSubSystem → 1 ≤ j →
    IsVeryAmple (H.toSubSystem.pow j)

end

end GroundTheory.Heights₂.Heights.Kleiman
