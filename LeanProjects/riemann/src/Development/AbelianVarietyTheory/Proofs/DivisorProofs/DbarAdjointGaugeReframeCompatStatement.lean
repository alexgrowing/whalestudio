import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAdjointGaugeReframeCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_adjoint_gauge_reframe_compat : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (h : Pt E g → ℝ) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → DifferentiableOn ℝ s (cov B g) → ∀ P ∈ cov B g, dbarAdj τ (fun Q => h (reframe τ γ Q)) (gauge n τ γ s) P = frameAt n τ γ P.1 (dbarAdj (fun b => moeb γ (τ b)) h s (reframe τ γ P)) := by
  first | exact @GlobalTheory.TorsionForm.Gauge.AdjConj.dbarAdj_gauge | exact GlobalTheory.TorsionForm.Gauge.AdjConj.dbarAdj_gauge | (intros; apply GlobalTheory.TorsionForm.Gauge.AdjConj.dbarAdj_gauge <;> assumption)
