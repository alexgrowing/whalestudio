import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaQuasiPeriodicNormalForm
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_quasi_periodic_normal_form : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ (c : Fl g → E → ℂ) (ψ : Pt E g → ℂ), DifferentiableOn ℂ ψ (cov U g) → (∀ P ∈ cov U g, ψ P ≠ 0) → (∀ l ∈ stdLat g, ∀ P ∈ cov U g, ψ (transl τ l P) = c l P.1 * ψ P) → ∃ a : E → Fin g → ℂ, DifferentiableOn ℂ a U ∧ ∀ P ∈ cov U g, ψ P = ψ (P.1, 0) * Complex.exp (a P.1 ⬝ᵥ P.2) := by
  first | exact @GlobalTheory.QuasiPeriodicExp.exp_linear_of_quasiPeriodic | exact GlobalTheory.QuasiPeriodicExp.exp_linear_of_quasiPeriodic | (intros; apply GlobalTheory.QuasiPeriodicExp.exp_linear_of_quasiPeriodic <;> assumption)
