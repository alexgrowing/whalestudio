import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReframe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_reframe : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → ContDiffOn ℝ ∞ (reframe τ γ) (cov B g) := by
  first | exact @GlobalTheory.ReframeSmooth.reframe_contDiffOn | exact GlobalTheory.ReframeSmooth.reframe_contDiffOn | (intros; apply GlobalTheory.ReframeSmooth.reframe_contDiffOn <;> assumption)
