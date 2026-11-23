import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalytic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricPullbackFamilyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDenseGoodPointsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem null_off_bigCell_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q), IsNull FA.Re.R.A {x | FA.pr (FA.Re.π x) ∈ BM.O l ∧ (FA.pr (FA.Re.π x) ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x))) (FA.Re.R.lift x x) p = 0)} := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l
  exact GlobalTheory.T.base_metric_pullback_family K ι Φ y Ψ N j M n BM _ FA.Re.R.X FA.Re.R.A FA.Re.R.U FA.Re.R.lift
    (FA.pr ∘ FA.Re.π) l (Pr.holoMap_comp' FA.Re.holo FA.pr_holo) (fun x => FA.Re.R.isOpen_U x)
    (fun x => FA.Re.R.mem_U x) (fun x p => FA.Re.R.holo x p)
    (fun x y' hy => FA.Re.R.compat x y' y' ⟨hy, FA.Re.R.mem_U y'⟩)
    (fun x hx V hV hxV => GlobalTheory.T.flag_analytic_dense_good_points K ι Φ y Ψ N j M n d BM FA l x hx V hV hxV)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
