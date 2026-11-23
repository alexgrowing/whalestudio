import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticPluckerColumnSwap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_plucker_column_swap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → ∀ (l : Fin BM.q) (x₀ : FA.Re.R.X), FA.pr (FA.Re.π x₀) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FA.Re.R.lift x₀ x₀) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), SameOrbit (FA.Re.R.lift x₀ x₀) (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FC.Lca τ ca cb c a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne <;> assumption)
