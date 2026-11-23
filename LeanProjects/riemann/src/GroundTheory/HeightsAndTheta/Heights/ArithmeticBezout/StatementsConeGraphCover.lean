import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def ConeGraphCover.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
    ∃ (e : ℕ → (Fin n ≃ Fin m ⊕ Fin (n - m))) (Ω : ℕ → Set (EuclideanSpace ℂ (Fin m)))
      (Φ : ℕ → EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m))),
      (∀ i, IsOpen (Ω i) ∧ DifferentiableOn ℂ (Φ i) (Ω i) ∧
        graphPt (e i) (Φ i) '' Ω i ⊆ coneSet h J ∧
        ∀ x ∈ Ω i, coneTangent h J (graphPt (e i) (Φ i) x) =
          LinearMap.range (fderiv ℂ (graphPt (e i) (Φ i)) x :
            EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))) ∧
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ ⋃ i, graphPt (e i) (Φ i) '' Ω i) = 0

end

end GroundTheory.Heights₂.Heights
