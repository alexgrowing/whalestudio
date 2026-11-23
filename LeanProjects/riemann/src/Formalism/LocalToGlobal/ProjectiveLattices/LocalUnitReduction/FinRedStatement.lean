import Mathlib

namespace Formalism.L2.Pj.LocalUnitReduction

def FinRedStatement : Prop :=
  ∀ (K' Fr : Type) [Field K'] [CommRing Fr] [Algebra K' Fr] (J : Ideal Fr)
    (ι : Type) [Fintype ι] (R : ι → Type) [∀ c, CommRing (R c)] [∀ c, Algebra K' (R c)]
    (φ : ∀ c, Fr →ₐ[K'] R c),
    (∀ f : Fr, (∀ c, φ c f = 0) → f = 0) →
    (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → ∀ c c', RingHom.ker (φ c) ≤ Q → RingHom.ker (φ c') ≤ Q → c = c') →
    (∀ c (r : R c), ∃ a p : Fr,
      (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → p ∉ Q) ∧ φ c p * r = φ c a) →
    (∀ c, FiniteDimensional K' (R c ⧸ Ideal.map (φ c) J) ∧ IsReduced (R c ⧸ Ideal.map (φ c) J)) →
    FiniteDimensional K' (Fr ⧸ J) ∧ IsReduced (Fr ⧸ J)

end Formalism.L2.Pj.LocalUnitReduction
