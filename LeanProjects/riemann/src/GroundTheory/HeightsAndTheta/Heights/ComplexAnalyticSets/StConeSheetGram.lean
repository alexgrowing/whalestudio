import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeChartGram
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def ConeSheetGram.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin e) (Fin n) ℂ) (f : EuclideanSpace ℂ (Fin n) → ℝ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
    IntegrableOn f {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}
      (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) →
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
          ∫ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, f z
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → z j = 0}).toReal *
          ∫ y, sheetSum (J ⊔ Ideal.span {linForm ℓ - 1}) A
            (fun _ s => ∫ t : ℂ, f (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s y)) *
              (‖t‖ ^ (2 * e) * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y)) y

end

end GroundTheory.Heights₂.Heights
