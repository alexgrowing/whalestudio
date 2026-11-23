import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionSmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnFormSmul
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superconnection_smul : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g n : ℕ) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (ρ : Pt E g → ℂ) (s : Pt E g → Ext (n + n + g)) (P : Pt E g), DifferentiableAt ℝ ρ P → DifferentiableAt ℝ s P → superconn τ h β u (fun Q => ρ Q • s Q) P = ρ P • superconn τ h β u s P + commOp τ β u ρ P (s P) := by
  first | exact @GlobalTheory.TorsionForm.Gauge.superconn_smul | exact GlobalTheory.TorsionForm.Gauge.superconn_smul | (intros; apply GlobalTheory.TorsionForm.Gauge.superconn_smul <;> assumption)
