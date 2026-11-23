import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnWedgeAnticomm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superconn_wedge_anticomm : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (k : Fin (n + n)) {σ : Pt E g → Ext (n + n + g)} {P : Pt E g}, DifferentiableAt ℝ σ P → superconn τ h β u (fun Q => wedge (k.castAdd g) (σ Q)) P = -wedge (k.castAdd g) (superconn τ h β u σ P) := by
  first | exact @GlobalTheory.TorsionForm.Odd.superconn_wedge | exact GlobalTheory.TorsionForm.Odd.superconn_wedge | (intros; apply GlobalTheory.TorsionForm.Odd.superconn_wedge <;> assumption)
