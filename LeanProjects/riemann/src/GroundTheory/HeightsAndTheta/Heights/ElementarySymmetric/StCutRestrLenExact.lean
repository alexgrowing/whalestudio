import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CutRestrLenExact.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (Lc : LineBundle k x) (s : Ω),
      IsSubvar x pp e → s ∈ Lc.secs → (∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) →
      ∀ Q : LineBundle k x, ∀ᶠ c : ℕ in atTop,
        restrLen pp ((Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ))) -
            restrLen pp (Q.toSubSystem.twist (twistSys k x (c : ℤ))) =
          restrLen (pp ⊔ zeroIdeal Lc.toSubSystem s)
            ((Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ)))

end

end GroundTheory.Heights₂.Heights.Kleiman
