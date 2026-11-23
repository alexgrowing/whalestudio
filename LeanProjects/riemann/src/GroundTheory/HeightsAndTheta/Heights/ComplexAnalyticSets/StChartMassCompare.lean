import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

open scoped ENNReal

noncomputable section

def ChartMassCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    (∀ k, SmoothNear (zeroSet J) (φ k)) →
      ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : (Fin n → ℂ) → ℝ, Measurable g →
        ∫⁻ y, ‖chartAbsDens J A ((Metric.closedBall 0 R).indicator g) φ y‖ₑ ≤
          K * ∫⁻ z in zeroSetEuc J ∩ {z | WithLp.ofLp z ∈ Metric.closedBall (0 : Fin n → ℂ) R},
            ‖g (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
