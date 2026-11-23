import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionBaseFunctionLeibniz
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DBaseApply
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge GlobalTheory.TorsionForm.Fibrewise
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superconnection_base_function_leibniz : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (ψ : E → ℂ) (r : Pt E g → Ext (n + n + g)) (P : Pt E g), DifferentiableAt ℝ ψ P.1 → DifferentiableAt ℝ r P → superconn τ h β u (fun Q => ψ Q.1 • r Q) P = ψ P.1 • superconn τ h β u r P + dBase β ψ P.1 (r P) := by
  first | exact @GlobalTheory.TorsionForm.Leibniz.superconn_fsmul | exact GlobalTheory.TorsionForm.Leibniz.superconn_fsmul | (intros; apply GlobalTheory.TorsionForm.Leibniz.superconn_fsmul <;> assumption)
