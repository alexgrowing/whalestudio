import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopChartIndependent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_top_chart_independent : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {ι : Type} [Fintype ι] {Δ : ι → Y.Dv} (m : ∀ i, (cxSt F).Met Y σ (Δ i)), IsMetricOn (ofDivisors Δ) ⊤ (lineGram (cxSt F) m) → ∀ (t : ι → ℝ) (c c' : GlobalTheory.AlgChart Y.str σ Y.dim) (y : Pts Y σ), y ∈ c.e.source → y ∈ c'.e.source → ∀ A ∈ (ofDivisors Δ).S (under y), chernTop ((∑ i, C (t i) * X (i, 1)) ^ Y.dim) (fun v => lineGram (cxSt F) m A (c.e.symm v)) (c.e y) = ‖transDet c.e c'.e y‖ ^ 2 * chernTop ((∑ i, C (t i) * X (i, 1)) ^ Y.dim) (fun v => lineGram (cxSt F) m A (c'.e.symm v)) (c'.e y) := by
  first | exact @GlobalTheory.ChernWeilLine.chernTop_lineGram_trans | exact GlobalTheory.ChernWeilLine.chernTop_lineGram_trans | (intros; apply GlobalTheory.ChernWeilLine.chernTop_lineGram_trans <;> assumption)
