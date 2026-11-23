import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutComponentSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def CutZeroNotLe.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp e →
    s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys x pp)).sub I) →
    ∃ f ∈ zeroIdeal L.toSubSystem s, f ∉ pp

end

end GroundTheory.Heights₂.Heights.Kleiman
