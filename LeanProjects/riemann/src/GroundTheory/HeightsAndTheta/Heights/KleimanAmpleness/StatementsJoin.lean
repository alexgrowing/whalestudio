import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def VeryAmpleTwistGenerated.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (L G : SubSystem k x Ω),
    (∀ I, ∃ L' : Submodule (chartRing k x I) Ω, L.sub I * L' = 1) →
    (∀ I, ∃ G' : Submodule (chartRing k x I) Ω, G.sub I * G' = 1) →
    IsVeryAmple L → G.Generated → IsVeryAmple (L.twist G)

section Hypotheses

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
