import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormSmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_form_smooth : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → ContDiffOn ℝ ∞ s (cov B g) → ∀ v : E, ContDiffOn ℝ ∞ (fun Q : Pt E g => connForm τ Q.1 v (s Q)) (cov B g) := by
  first | exact @GlobalTheory.TorsionForm.ConnSmooth.connForm_contDiffOn | exact GlobalTheory.TorsionForm.ConnSmooth.connForm_contDiffOn | (intros; apply GlobalTheory.TorsionForm.ConnSmooth.connForm_contDiffOn <;> assumption)
