import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityTimeDerivative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.energy_density_time_derivative : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (u : ℝ → Mat n → W), Sm u → ∀ (s : ℝ), ∀ y ∈ GLs n, HasDerivAt (fun r => dens u r y) (2 * ⟪dt (dt u) s y, dt u s y⟫_ℝ + (1 / 2) * ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ + 2 * ⟪dt u s y, u s y⟫_ℝ) s := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens | exact GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens <;> assumption)
