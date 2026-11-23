import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnCompositionWithAnalyticMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_gram_comp_basePoint :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n)  (l : Fin BM.q) (τ' : Ψ) (Un : Set (Fin d → ℂ)) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s) → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => BM.G l τ' (bp w) r s) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM l τ' Un bp hU hbp han hmem r t
  have hre := contDiffOn_comp_of_analytic_in_charts _ _ _ BM.Rb.A Un bp _ _ hU hbp han hmem
    (BM.G_smooth l τ' r t).1
  have him := contDiffOn_comp_of_analytic_in_charts _ _ _ BM.Rb.A Un bp _ _ hU hbp han hmem
    (BM.G_smooth l τ' r t).2
  have h1 := Complex.ofRealCLM.contDiff.comp_contDiffOn hre
  have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn him
  have h3 := h1.add (h2.mul (contDiffOn_const (c := Complex.I)))
  refine h3.congr ?_
  intro w _
  simp [Complex.re_add_im]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
