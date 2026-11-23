import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightMapAntisymmetricDeltaIdentity
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vandermonde_product_weight_positive : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (v : ℝ), (∀ c : Ψ × Fin N → ℝ, eval c Q = v * ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m)) → toWt Q = C v * antisymDelta Ψ N ∧ 0 < eval (rhoWt Ψ N) (antisymDelta Ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta | exact GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta <;> assumption)
