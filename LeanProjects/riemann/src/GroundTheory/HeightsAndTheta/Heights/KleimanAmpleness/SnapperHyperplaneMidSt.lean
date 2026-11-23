import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SnapperHyperplaneMid.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ i : Fin (N + 1), (X i : Poly k N) ∉ pp →
    ∀ (a : ℤ) (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
      eulerCharQuot k
          ((((twistSys k x (a + 1)).twist (idealSys x (pp ⊔ Ideal.span {(X i : Poly k N)}))).twistPows t
            (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          ((((twistSys k x (a + 1)).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
            (twistSys k x c)) =
        pieceChar k pp a L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
