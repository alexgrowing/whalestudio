import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDenseGoodPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_dense_good_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q) (x : FA.Re.R.X), FA.pr (FA.Re.π x) ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, FA.pr (FA.Re.π x') ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x'))) (FA.Re.R.lift x' x') p ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_r | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_r | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_r <;> assumption)
