import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def InterNumRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (pp : Ideal (Poly k N)) (n : ℕ), IsSubvar y pp n →
    ∀ (L : Fin n → LineBundle k x) (L' : Fin n → LineBundle k y) (r : Fin n → Ω → K'),
      (∀ i, RestrictData (L i).toSubSystem hxy (L' i).toSubSystem (r i)) →
      interNum pp (fun i => (L' i).toSubSystem) = interNum pp (fun i => (L i).toSubSystem)

end

end GroundTheory.Heights₂.Heights.Kleiman
