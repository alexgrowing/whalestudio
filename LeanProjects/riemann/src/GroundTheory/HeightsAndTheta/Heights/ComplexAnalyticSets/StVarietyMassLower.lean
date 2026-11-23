import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def VarietyMassLower.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ∀ R : ℝ,
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R → ∀ ρ ∈ Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal (c * ρ ^ (2 * d)) ≤
          μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ)

end

end GroundTheory.Heights₂.Heights
