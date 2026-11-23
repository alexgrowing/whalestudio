import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RatChartObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

def RatFibreAvoid.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q f : MvPolynomial (Fin n) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → f ∉ J →
      ∀ᵐ (y : Fin d → ℂ), ∀ x ∈ RatChart.ratFibre J p q y, eval x f ≠ 0

end GroundTheory.Heights₂.Heights
