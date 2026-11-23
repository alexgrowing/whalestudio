import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GapEqWeightSubNext
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_polynomial_homogeneous_coeff_bound : ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ, (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWt Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWt Q)| ≤ Cst * M)) ∧ ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWtS Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWtS Q)| ≤ Cst * M) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.toWt_toWtS_homogeneous_coeff_bound | exact GlobalTheory.CompanionTheory.Ar.PB.toWt_toWtS_homogeneous_coeff_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.toWt_toWtS_homogeneous_coeff_bound <;> assumption)
