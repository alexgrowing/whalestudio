import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def RestrLenEuler.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (qq : Ideal (Poly k N)), (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) →
    primeOf (S := k) x ≤ qq → ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∀ᶠ c : ℤ in atTop,
        restrLen qq (((twistSys k x 0).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          pieceChar k qq 0 L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
