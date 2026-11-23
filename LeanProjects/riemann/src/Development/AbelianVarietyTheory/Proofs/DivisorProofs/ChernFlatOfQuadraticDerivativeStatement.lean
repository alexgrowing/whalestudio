import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFlatOfQuadraticDerivative
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReQuad
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.ThetaMet
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_flat_of_quadratic_derivative : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ContDiffOn ℝ ∞ (flat τ) (cov B g) → ContDiffOn ℝ ∞ (quad τ) (cov B g) → ContDiffOn ℝ ∞ (reQuad τ) (cov B g) → (∀ P ∈ cov B g, ∀ v : Pt E g, fderiv ℝ (quad τ) P (Complex.I • v) = fderiv ℝ (reQuad τ) P v + 2 * ∑ i, flat τ P (Sum.inl i) * dflat τ P v (Sum.inr i)) → ChernIsFlat B τ (fun P => Real.exp (-2 * π * quad τ P)) := by
  first | exact @GlobalTheory.ThetaMetDdc.chernIsFlat_exp_quad | exact GlobalTheory.ThetaMetDdc.chernIsFlat_exp_quad | (intros; apply GlobalTheory.ThetaMetDdc.chernIsFlat_exp_quad <;> assumption)
