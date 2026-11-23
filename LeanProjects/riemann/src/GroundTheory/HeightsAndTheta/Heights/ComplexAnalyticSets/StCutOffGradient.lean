import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def CutOffGradient.Statement : Prop :=
  ∃ K : ℝ, ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (k : ℕ)
    (y : Fin (d + 1) → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
        (vecCons (logLogCutAlong A P k) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y ∧
    chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
        (vecCons (fun x => logLogCutAlong A P k x ^ 2 / 2) φ) y ≤
      K / ((k : ℝ) + 1) * tubeDens J A P R φ y ∧
    chartAbsDens J A ((Metric.closedBall 0 R).indicator (logLogCutAlong A P k))
        (vecCons (logLogCutAlong A P k) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y

end

end GroundTheory.Heights₂.Heights
