import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOneParamDifferentiable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_one_param_differentiable : ∀ {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (Φ : ℝ → 𝔸), Continuous Φ → Φ 0 = 1 → (∀ s t, Φ (s + t) = Φ s * Φ t) → ∃ B, HasDerivAt Φ B 0 := by
  first | exact @GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam | exact GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam | (intros; apply GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam <;> assumption)
