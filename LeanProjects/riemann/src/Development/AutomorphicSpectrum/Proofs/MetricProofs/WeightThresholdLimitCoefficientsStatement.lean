import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightThresholdLimitCoefficients
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_threshold_limit_coefficients : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ) (u : Wt Ψ N) (g : ℝ) (c : T.Comp) (s : ℕ → ℝ) (q : ℕ → ℕ) (m : ℕ → Option (Ψ × Fin N) → ℤ), IsFullIntersectionSystem II → T.T1 II → WeightHyp T.j u g → bigB0 u g < B + 1 → (∀ n, 0 < s n) → Tendsto s atTop (𝓝 0) → (∀ n, 0 < q n) → (∀ n j, (m n j : ℝ) = q n * (T.M B c).coef (T.lamS u (s n)) (s n) j) → (∀ᶠ n in atTop, IsNefH (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n))) ∧ Tendsto (fun n => geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / (q n : ℝ) ^ dimFl Ψ N) atTop (𝓝 ((T.M B c).δ * (T.vol c * flagDeg u))) ∧ Tendsto (fun n => normHt II (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / q n) atTop (𝓝 (T.slope II B c u)) ∧ 0 < T.vol c * flagDeg u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.tower_seq | exact GlobalTheory.CompanionTheory.Ar.Small.tower_seq | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.tower_seq <;> assumption)
