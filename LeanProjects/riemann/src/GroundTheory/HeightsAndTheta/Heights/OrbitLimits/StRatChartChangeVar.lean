import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RatChartObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

def RatChartChangeVar.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ComplexSets.IsFiniteProjection J A →
    q ∉ J → (∀ y, (RatChart.ratFibre J p q y).Finite) → Measurable f →
    (∀ k, SmoothNear (ComplexSets.zeroSet J) (φ k)) →
      AEStronglyMeasurable (RatChart.ratDens J p q f φ) volume ∧
      AEStronglyMeasurable (RatChart.ratAbsDens J p q f φ) volume ∧
      (Integrable (RatChart.ratAbsDens J p q f φ) →
        Integrable (chartAbsDens J A f φ) ∧ ∫ y, RatChart.ratDens J p q f φ y = chartInt J A f φ)

end GroundTheory.Heights₂.Heights
