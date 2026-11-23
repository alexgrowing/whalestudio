import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOnLineGram
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMetricOn_line_gram : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y) {ι : Type} [Fintype ι] {Δ : ι → Y.Dv} (m : ∀ i σ, (cxSt F).Met Y σ (Δ i)) (a : Fin (M.n + 1)) (Q : ι → LocPot (M.X a)), (∀ i, IsPot (I.pt a) (m i (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) → IsMetricOn (ofDivisors Δ) ⊤ (lineGram (cxSt F) fun i => m i (I.ε a)) := by
  first | exact @GlobalTheory.ChernWeilLine.isMetricOn_lineGram_of_isPot | exact GlobalTheory.ChernWeilLine.isMetricOn_lineGram_of_isPot | (intros; apply GlobalTheory.ChernWeilLine.isMetricOn_lineGram_of_isPot <;> assumption)
