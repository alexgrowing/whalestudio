import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

def VarWirtinger.Statement : Prop :=
  ∀ d : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ),
      J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
        Integrable (chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
            (fun _ => euclPot)) ∧
          μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ B) =
            ENNReal.ofReal (c * ∫ y, chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
              (fun _ => euclPot) y)

end

end GroundTheory.Heights₂.Heights
