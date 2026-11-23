import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionWedgeAnticommute
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DBaseApply
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge GlobalTheory.TorsionForm.Fibrewise
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superconnection_wedge_anticommute : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (k : Fin (n + n + g)) (r : Pt E g → Ext (n + n + g)) (P : Pt E g), (∀ a, k ≠ dzb n a) → DifferentiableAt ℝ r P → superconn τ h β u (fun Q => wedge k (r Q)) P = -wedge k (superconn τ h β u r P) := by
  first | exact @GlobalTheory.TorsionForm.WedgeBase.superconn_wedge | exact GlobalTheory.TorsionForm.WedgeBase.superconn_wedge | (intros; apply GlobalTheory.TorsionForm.WedgeBase.superconn_wedge <;> assumption)
