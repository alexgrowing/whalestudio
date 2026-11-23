import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaPieceSmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nabla_piece_smooth : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ContDiffOn ℝ ∞ s (cov B g) → ∀ (i : Fin n) (v : E), ContDiffOn ℝ ∞ (fun Q => nabPiece τ h s Q i v) (cov B g) := by
  first | exact @GlobalTheory.TorsionForm.Pullback.PieceSmooth.nabPiece_contDiffOn | exact GlobalTheory.TorsionForm.Pullback.PieceSmooth.nabPiece_contDiffOn | (intros; apply GlobalTheory.TorsionForm.Pullback.PieceSmooth.nabPiece_contDiffOn <;> assumption)
