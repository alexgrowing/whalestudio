import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereRegularizationLogLogBound
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_regularization_log_log_bound : ConvergenceRateStatement → ∀ (e : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ), 0 < S.t₀ → ∃ C' t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ S.t₀ ∧ ∀ t t', 0 < t' → t' ≤ t → t ≤ t₁ → ∀ (a : σ) (w : Fin e → σ) (c : Fin e → Bool), |mInt S.A (fun i => S.potT (w i) (if c i then t else t')) (fun x => S.phT a t x - S.phT a t' x)| ≤ C' * Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.signed_rate | exact GlobalTheory.CompanionTheory.Ar.PB.signed_rate | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.signed_rate <;> assumption)
