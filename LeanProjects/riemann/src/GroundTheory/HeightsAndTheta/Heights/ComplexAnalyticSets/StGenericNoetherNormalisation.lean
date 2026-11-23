import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

universe u

def GenericNoetherNormalisation.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] (n : ℕ) (q : Ideal (MvPolynomial (Fin (n + 1)) A)),
    q.IsPrime → q ≠ ⊥ → q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥ →
    ∃ a : A, a ≠ 0 ∧ ∃ (z : Fin n → MvPolynomial (Fin (n + 1)) A ⧸ q)
      (s : Finset (MvPolynomial (Fin (n + 1)) A ⧸ q)),
      ∀ d : MvPolynomial (Fin (n + 1)) A ⧸ q, ∃ (k : ℕ) (c : MvPolynomial (Fin (n + 1)) A ⧸ q → MvPolynomial (Fin n) A),
        a ^ k • d = ∑ t ∈ s, aeval z (c t) * t

end GroundTheory.Heights₂.Heights
