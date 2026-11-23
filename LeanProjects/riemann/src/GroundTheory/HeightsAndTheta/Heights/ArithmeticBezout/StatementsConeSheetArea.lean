import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeChartArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFibre
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)

def chosenSheet {n e : ℕ} (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ)
    (w : ((k : Unit) → PBlk n k) → ℂ) : (Fin e → ℂ) → (Σ k, PBlk n k) → ℂ := by
  classical
  exact if hγ : ∃ γ, IsSheet P Ψ y w γ then hγ.choose else 0

def ConeSheetArea.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (f : EuclideanSpace ℂ (Fin n) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      IntegrableOn f (coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P))
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) →
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
          ∫ y in coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P), f y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal *
          ∫ x : Fin e → ℂ, ∑ᶠ w ∈ fibre P Ψ x, ∫ t : ℂ,
            f (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
              (‖t‖ ^ (2 * e) *
                gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)

end GroundTheory.Heights₂.Heights
