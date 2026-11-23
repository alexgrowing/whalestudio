import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedFlagDegreeLowerBound
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_flag_degree_lower_bound : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ) (Λ μ C : ℝ), (∀ τ, Antitone (lam τ)) → (∀ τ i, |lam τ i| ≤ Λ) → 0 ≤ μ → E.slopeMax ≤ (μ : EReal) → (∀ τ, |A.flatDeg τ| ≤ C) → -(Fintype.card Ψ * (2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C)) ≤ A.lamDeg lam := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower | exact GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower | (intros; apply GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower <;> assumption)
