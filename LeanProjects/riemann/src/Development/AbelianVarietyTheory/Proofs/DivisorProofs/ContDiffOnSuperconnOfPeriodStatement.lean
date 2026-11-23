import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnSuperconnOfPeriod
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_superconn_of_period : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ContDiffOn ℝ ∞ s (cov B g) → ContDiffOn ℝ ∞ (superconn τ h β u s) (cov B g) := by
  first | exact @GlobalTheory.TorsionForm.SuperconnSmoothCov.superconn_contDiffOn_cov | exact GlobalTheory.TorsionForm.SuperconnSmoothCov.superconn_contDiffOn_cov | (intros; apply GlobalTheory.TorsionForm.SuperconnSmoothCov.superconn_contDiffOn_cov <;> assumption)
