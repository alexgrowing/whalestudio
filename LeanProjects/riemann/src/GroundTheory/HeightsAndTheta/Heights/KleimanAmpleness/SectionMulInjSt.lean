import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SectionMulInj.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp →
    ∀ (D M : LineBundle k x) (s : Ω), (∃ f ∈ zeroIdeal D.toSubSystem s, f ∉ pp) →
    ∀ (I : Chart x), ∀ y ∈ M.sub I,
      s * y ∈ ((M.toSubSystem.twist D.toSubSystem).twist (idealSys x pp)).sub I →
      y ∈ (M.toSubSystem.twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
