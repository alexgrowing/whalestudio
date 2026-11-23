import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RatChartObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

def RatSheetNoChartNull.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ComplexSets.IsFiniteProjection J A →
    (∀ y, (RatChart.ratFibre J p q y).Finite) →
      volume (RatChart.ratMap p q ''
        {x | x ∈ ComplexSets.zeroSet J ∧ (∃ s, RatChart.IsRatSheetAt J p q x s) ∧
          ¬ ∃ s', IsSheetAt J A x s'}) = 0

end GroundTheory.Heights₂.Heights
