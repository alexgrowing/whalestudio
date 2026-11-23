import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RatChartObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

def ChartSheetNoRatNull.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ComplexSets.IsFiniteProjection J A →
    q ∉ J → (∀ y, (RatChart.ratFibre J p q y).Finite) →
      volume ((fun x => A *ᵥ x) ''
        {x | x ∈ ComplexSets.zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧
          ¬ ∃ s', RatChart.IsRatSheetAt J p q x s'}) = 0

end GroundTheory.Heights₂.Heights
