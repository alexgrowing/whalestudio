import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionFibreGauge
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnFormSmul
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superconnection_fibre_gauge : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (ρ : Pt E g → ℂ) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ContDiffOn ℝ ∞ ρ (cov B g) → ContDiffOn ℝ ∞ s (cov B g) → ∀ b ∈ B, (∀ y, ρ (b, y) = 1) → ∀ z, superconn τ h β u (fun Q => ρ Q • superconn τ h β u s Q + commOp τ β u ρ Q (s Q)) (b, z) = superconn τ h β u (superconn τ h β u s) (b, z) := by
  first | exact @GlobalTheory.TorsionForm.FibreSq.superconn_sq_fibre | exact GlobalTheory.TorsionForm.FibreSq.superconn_sq_fibre | (intros; apply GlobalTheory.TorsionForm.FibreSq.superconn_sq_fibre <;> assumption)
