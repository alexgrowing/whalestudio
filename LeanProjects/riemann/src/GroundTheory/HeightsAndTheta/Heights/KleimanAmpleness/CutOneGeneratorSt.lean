import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutNonemptySt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def CutOneGenerator.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs →
    ¬ ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), L.sub (singleChart hj) ≤
      (L.twist (idealSys x pp)).sub (singleChart hj) ⊔
        Submodule.span (chartRing k x (singleChart hj)) {s}

end

end GroundTheory.Heights₂.Heights.Kleiman
