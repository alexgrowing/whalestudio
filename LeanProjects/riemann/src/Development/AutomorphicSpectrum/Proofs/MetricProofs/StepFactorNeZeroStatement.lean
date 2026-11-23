import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.StepFactorNeZero
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_factor_ne_zero : ∀ (N j : ℕ) (a i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j h → h.det ≠ 0 → facOf N j a h i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero <;> assumption)
