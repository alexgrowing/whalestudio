import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncidenceZeroLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def FormsThroughPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsProjPrime Q →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((k : ℕ) : WithBot ℕ∞) →
    ∀ x : Fin n → AlgebraicClosure F, x ≠ 0 → (∃ q ∈ Q, aeval x q ≠ 0) →
      ∃ u : Fin k × Fin n → AlgebraicClosure F, (∀ i, ∑ j, u (i, j) * x j = 0) ∧ u ∉ incidence Q k

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
