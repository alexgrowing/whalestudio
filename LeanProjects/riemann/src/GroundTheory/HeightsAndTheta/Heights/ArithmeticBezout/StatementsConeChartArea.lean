import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeChart
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)

def chartGramDensity {n e : ℕ} (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (S : Matrix (Fin n) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (y : Fin e → ℂ) (w : ((k : Unit) → PBlk n k) → ℂ) : ℝ := by
  classical
  exact if hγ : ∃ γ, IsSheet P Ψ y w γ then
    g (fun i => hγ.choose y ⟨(), i⟩) *
      ((e.factorial : ℝ) / Real.pi ^ e *
          gramVol (fun y' => S *ᵥ fun i => hγ.choose y' ⟨(), i⟩) y /
        ‖WithLp.toLp 2 (S *ᵥ fun i => hγ.choose y ⟨(), i⟩)‖ ^ (2 * (e + 1)))
  else 0

def ConeChartArea.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : (Fin n → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → Measurable g →
      (∀ (c : ℂ) (z : Fin n → ℂ), c ≠ 0 → g (c • z) = g z) →
      IntegrableOn (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧
          ∀ q ∈ complexFibreIdeal P, eval ((ObjectsHeight.ofPointMatrix S hS).pointOf y) q = 0}
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) →
      coneIntegral (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) e g =
        ∫ y, ∑ᶠ w ∈ fibre P Ψ y, chartGramDensity P Ψ S g y w

end GroundTheory.Heights₂.Heights
