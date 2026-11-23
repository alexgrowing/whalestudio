import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionIsometry
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnFormSmul
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superconnection_isometry : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g n : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h h' : Pt E g → ℝ) (φ : Pt E g → ℂ) (β : Fin n → E) (u : ℝ) (s : Pt E g → Ext (n + n + g)) (P : Pt E g), IsOpen B → P ∈ cov B g → DifferentiableOn ℂ φ (cov B g) → (∀ Q ∈ cov B g, φ Q ≠ 0) → (∀ Q ∈ cov B g, 0 < h Q) → DifferentiableAt ℝ h P → IsIsometry B h h' φ → DifferentiableAt ℝ s P → superconn τ h' β u (fun Q => φ Q • s Q) P = φ P • superconn τ h β u s P := by
  first | exact @GlobalTheory.TorsionForm.Gauge.superconn_isometry_smul | exact GlobalTheory.TorsionForm.Gauge.superconn_isometry_smul | (intros; apply GlobalTheory.TorsionForm.Gauge.superconn_isometry_smul <;> assumption)
