import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCUnif

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), n = Fintype.card Ψ * j * (N - j) → d + 1 = antisymDegree Ψ N → IsUniformised (FA.S.comap some).A (FA.S.comap some).open' j (FA.S.comap some).potH := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA _ _
  refine ⟨?_, ?_⟩
  · intro x hx
    have hb := (PositivityTheory.Xgp.c_unif.mem_open_iff FA x).1 hx
    obtain ⟨l, hl⟩ := BM.O_cover (FA.pr x)
    obtain ⟨V, Pi, hxV, hP⟩ := BM.period l (FA.pr x) ⟨hl, hb⟩
    obtain ⟨V', g, hc, -⟩ := PositivityTheory.Xgp.c_unif.chart_over FA x ⟨hl, hb⟩ hxV hP
    exact ⟨V', g, hc⟩
  · obtain ⟨l, b, ⟨hbO, hbs⟩, V, Pi, hbV, hP, himm⟩ := BM.immersion
    obtain ⟨x, rfl⟩ := PositivityTheory.Xgp.c_unif.exists_over FA hbO
    have hx : x ∈ (FA.S.comap some).open' := (PositivityTheory.Xgp.c_unif.mem_open_iff FA x).2 hbs
    obtain ⟨V', g, hc, hi⟩ := PositivityTheory.Xgp.c_unif.chart_over FA x ⟨hbO, hbs⟩ hbV hP
    exact ⟨x, hx, V', g, hc, hi himm⟩
