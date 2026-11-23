import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMetricChernFlat
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_metric_chern_flat : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → IsMetric B τ (stdLat g) (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2)) (fun P : Pt E g => Real.exp (-2 * π * ((fun i => (P.2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im)))) ∧ ChernIsFlat B τ (fun P : Pt E g => Real.exp (-2 * π * ((fun i => (P.2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im)))) := by
  first | exact @GlobalTheory.ThetaMet.isMetric_chernIsFlat | exact GlobalTheory.ThetaMet.isMetric_chernIsFlat | (intros; apply GlobalTheory.ThetaMet.isMetric_chernIsFlat <;> assumption)
