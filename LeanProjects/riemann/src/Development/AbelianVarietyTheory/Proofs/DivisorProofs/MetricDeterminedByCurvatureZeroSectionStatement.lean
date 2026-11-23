import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricDeterminedByCurvatureZeroSection
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_determined_by_curvature_zero_section : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (h₁ h₂ : Pt E g → ℝ), IsMetric B τ (stdLat g) j h₁ → IsMetric B τ (stdLat g) j h₂ → (∀ P ∈ cov B g, ∀ v w : Pt E g, ddc (fun Q => Real.log (h₁ Q)) P v w = ddc (fun Q => Real.log (h₂ Q)) P v w) → (∀ b ∈ B, h₁ (zeroSec g b) = h₂ (zeroSec g b)) → Set.EqOn h₁ h₂ (cov B g) := by
  first | exact @GlobalTheory.MetricUniq.metric_eq_of_ddc_eq | exact GlobalTheory.MetricUniq.metric_eq_of_ddc_eq | (intros; apply GlobalTheory.MetricUniq.metric_eq_of_ddc_eq <;> assumption)
