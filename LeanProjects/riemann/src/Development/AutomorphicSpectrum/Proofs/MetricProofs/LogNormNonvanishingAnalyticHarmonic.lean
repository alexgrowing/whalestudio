import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem log_norm_eventually_eq_re_analyticAt :
    ∀ (e : ℕ) (f : (Fin e → ℂ) → ℂ) (z : Fin e → ℂ), AnalyticAt ℂ f z → f z ≠ 0 →
      ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, Real.log ‖f z'‖ = (Hh z').re := by
  intro e f z hf hz
  refine ⟨fun z' => Complex.log (f z' * (f z)⁻¹) + Complex.log (f z), ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun z' => f z' * (f z)⁻¹) z := hf.mul analyticAt_const
    have h2 : AnalyticAt ℂ Complex.log (f z * (f z)⁻¹) := by
      apply analyticAt_clog
      rw [mul_inv_cancel₀ hz]
      exact Complex.one_mem_slitPlane
    exact (AnalyticAt.comp (f := fun z' => f z' * (f z)⁻¹) (x := z) h2 h1).add analyticAt_const
  · filter_upwards [hf.continuousAt.eventually_ne hz] with z' hz'
    simp only [Complex.add_re, Complex.log_re, norm_mul, norm_inv]
    rw [Real.log_mul (norm_ne_zero_iff.2 hz') (inv_ne_zero (norm_ne_zero_iff.2 hz)), Real.log_inv]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
