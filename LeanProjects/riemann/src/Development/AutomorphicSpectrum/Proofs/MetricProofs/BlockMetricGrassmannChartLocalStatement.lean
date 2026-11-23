import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricGrassmannChartLocal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_metric_grassmann_chart_local : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → ∃ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ), IsBlockDiag j h ∧ h.det ≠ 0 ∧ a ≠ 0 ∧ (∀ I, IsStepRows N j p.2 I → plk M (BM.F l) k₀ z I = a * minorIJ h I (stepCols N j p.2)) ∧ ∀ m : ι k₀, z ⟨k₀, m⟩ = a * ∑ I, valAt M.x ((BM.F l).u ⟨k₀, m⟩ I) (basePart M.blk z) * minorIJ h I (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint.main <;> assumption)
