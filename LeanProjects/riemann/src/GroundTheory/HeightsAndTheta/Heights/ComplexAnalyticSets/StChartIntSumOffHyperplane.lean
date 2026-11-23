import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def ChartIntSumOffHyperplane.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (u : Fin n → ℂ)
    (m : ℕ) (f : (Fin n → ℂ) → ℝ) (F : Fin m → (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    linForm u ∉ J →
    (∀ x ∈ zeroSet J, linEval u x ≠ 0 → f x = ∑ b, F b x) →
    (∀ b, Integrable (chartDens J A (F b) φ)) →
      chartInt J A f φ = ∑ b, chartInt J A (F b) φ

end

end GroundTheory.Heights₂.Heights
