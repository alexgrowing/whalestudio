import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFormsThroughPoint
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PComponentOfIncIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartZeroTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (n d : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsProjPrime Q →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞) →
    ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (y : Fin n → Ω) (j : Fin n),
      (∀ q ∈ Q, aeval y q = 0) → y j ≠ 0 →
        Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => y m * (y j)⁻¹)) ≤ (d : Cardinal)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
