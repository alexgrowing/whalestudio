import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPlusAdjointSmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_plus_adjoint_smooth : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ContDiffOn ℝ ∞ s (cov B g) → ContDiffOn ℝ ∞ (fun Q => dbarV s Q + dbarAdj τ h s Q) (cov B g) := by
  first | exact @GlobalTheory.DbarSmooth.dbar_add_adj_smooth | exact GlobalTheory.DbarSmooth.dbar_add_adj_smooth | (intros; apply GlobalTheory.DbarSmooth.dbar_add_adj_smooth <;> assumption)
