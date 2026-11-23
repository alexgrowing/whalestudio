import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnSquarePeriodFunction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superconn_square_period_function : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ {h : Pt E g → ℝ}, ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ∀ (β : Fin n → E) (u : ℝ) {ψ : E → Fin g → ℂ}, ContDiffOn ℝ ∞ ψ B → ∀ {b : E}, b ∈ B → ∀ {f : (Fin g → ℂ) → Ext (n + n + g)}, ContDiff ℝ ∞ f → ∀ (z : Fin g → ℂ), superconn τ h β u (superconn τ h β u fun P => f (P.2 + ψ P.1)) (b, z) = superconn τ h β u (superconn τ h β u fun P => f (P.2 + ψ b)) (b, z) := by
  first | exact @GlobalTheory.TorsionForm.CurvExt.superconn_sq_shift | exact GlobalTheory.TorsionForm.CurvExt.superconn_sq_shift | (intros; apply GlobalTheory.TorsionForm.CurvExt.superconn_sq_shift <;> assumption)
