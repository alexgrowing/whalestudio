import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def SectionCount.Drop.Term.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (b : ℕ) (pp : Ideal (Poly k N)) (e : ℕ) (c : ℤ),
    IsVeryAmple Nb.toSubSystem → IsSubvar x pp e →
    ∃ c' : ℕ, ∀ n i : ℕ,
      Module.Finite k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c') 0)
        ((twistMul Nb.toSubSystem (n + c') 0).twist (idealSys x pp)) 0) ∧
      Module.finrank k (SubSystem.quotH
          ((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x c))
          (((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x c)).twist
            (idealSys x pp)) 0) ≤
        Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c') 0)
          ((twistMul Nb.toSubSystem (n + c') 0).twist (idealSys x pp)) 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
