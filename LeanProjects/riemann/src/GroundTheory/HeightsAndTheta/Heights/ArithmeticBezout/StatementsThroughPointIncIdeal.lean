import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncidenceZeroLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ThroughPointIncIdeal.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)) (x c : Fin n → AlgebraicClosure F),
    ∑ j, c j * x j = 1 →
    (∀ u : Fin k × Fin n → AlgebraicClosure F, (∀ i, ∑ j, u (i, j) * x j = 0) → u ∈ incidence Q k) →
      ∀ g ∈ incIdeal Q k, aeval (genSubst (k := k) x c) g = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
