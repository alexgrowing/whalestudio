import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def AffineChartTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (j : Fin n), IsProjPrime P →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞) → X j ∉ P →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)) =
        ((d : ℕ) : Cardinal)

section Inhabitants

theorem AffineChartTrdeg.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      ringKrullDim (MvPolynomial (Fin 1) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) =
        ((0 + 1 : ℕ) : WithBot ℕ∞) ∧
      (X 0 : MvPolynomial (Fin 1) ℚ) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  ⟨isProjPrime_point ℚ, ringKrullDim_quot_bot ℚ 1, by rw [Ideal.mem_bot]; exact X_ne_zero 0⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights
