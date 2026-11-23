import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def VeryAmpleProductPos.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (Ls : Fin e → LineBundle k x), IsSubvar x pp e →
    (∀ i, IsVeryAmple (Ls i).toSubSystem) → 0 < interNum pp (fun i => (Ls i).toSubSystem)

end

end GroundTheory.Heights₂.Heights.Kleiman
