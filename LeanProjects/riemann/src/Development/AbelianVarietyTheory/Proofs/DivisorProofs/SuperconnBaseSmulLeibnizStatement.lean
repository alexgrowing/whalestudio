import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnBaseSmulLeibniz
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superconn_base_smul_leibniz : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) {φ : E → ℂ} {σ : Pt E g → Ext (n + n + g)} {P : Pt E g}, DifferentiableAt ℝ φ P.1 → DifferentiableAt ℝ σ P → superconn τ h β u (fun Q => φ Q.1 • σ Q) P = φ P.1 • superconn τ h β u σ P + baseD β φ P.1 (σ P) := by
  first | exact @GlobalTheory.TorsionForm.superconn_fst_smul | exact GlobalTheory.TorsionForm.superconn_fst_smul | (intros; apply GlobalTheory.TorsionForm.superconn_fst_smul <;> assumption)
