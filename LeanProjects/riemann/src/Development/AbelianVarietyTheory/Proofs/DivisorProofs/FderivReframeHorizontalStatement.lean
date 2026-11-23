import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivReframeHorizontal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fderiv_reframe_horizontal : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → ∀ P ∈ cov B g, ∀ v : E, fderiv ℝ (reframe τ γ) P (hor τ P v) = hor (fun b => moeb γ (τ b)) (reframe τ γ P) v := by
  first | exact @GlobalTheory.TorsionForm.ReframeHor.fderiv_reframe_hor | exact GlobalTheory.TorsionForm.ReframeHor.fderiv_reframe_hor | (intros; apply GlobalTheory.TorsionForm.ReframeHor.fderiv_reframe_hor <;> assumption)
