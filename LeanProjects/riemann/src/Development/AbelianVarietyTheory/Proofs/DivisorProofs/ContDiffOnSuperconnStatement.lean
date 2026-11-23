import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnSuperconn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_superconn' : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ {h : Pt E g → ℝ}, ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ∀ (β : Fin n → E) (u : ℝ) {σ : Pt E g → Ext (n + n + g)}, ContDiffOn ℝ ∞ σ (cov B g) → ContDiffOn ℝ ∞ (superconn τ h β u σ) (cov B g) := by
  first | exact @GlobalTheory.SuperconnSmooth.main | exact GlobalTheory.SuperconnSmooth.main | (intros; apply GlobalTheory.SuperconnSmooth.main <;> assumption)
