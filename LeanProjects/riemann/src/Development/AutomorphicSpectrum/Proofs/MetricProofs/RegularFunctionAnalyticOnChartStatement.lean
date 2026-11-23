import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionAnalyticOnChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbitStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_function_analytic_on_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (s : Ω) (e n : ℕ) (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (Un : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → Rb.X) (w₀ : Fin e → ℂ), IsOpen Un → w₀ ∈ Un → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (Rb.A.chart k).source)) → RegAt x (mCoordIdeal (Rb.lift (bp w₀) (bp w₀))) s → AnalyticAt ℂ (fun w => valAt x s (Rb.lift (bp w) (bp w))) w₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.analyticAt_valAt_lift_family | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.analyticAt_valAt_lift_family | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.analyticAt_valAt_lift_family <;> assumption)
