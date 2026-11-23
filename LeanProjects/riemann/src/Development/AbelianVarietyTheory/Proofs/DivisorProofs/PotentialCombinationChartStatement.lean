import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialCombinationChart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potential_combination_chart : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {M : Man Y.dim} (I : ManIs M Y) {ι : Type} [Fintype ι] {Δ : ι → Y.Dv} (m : ∀ i σ, (cxSt F).Met Y σ (Δ i)) (t : ι → ℝ) (a : Fin (M.n + 1)) (Q : ι → LocPot (M.X a)), (∀ i, IsPot (I.pt a) (m i (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) → ∀ (j : Fin (M.A a).n) (c : GlobalTheory.AlgChart Y.str (I.ε a) Y.dim), (M.A a).chart j = (I.pt a).transOpenPartialHomeomorph c.finChart → ∀ z ∈ ((M.A a).chart j).target, ∀ A ∈ (ofDivisors Δ).S (under (c.finChart.symm z)), locDens (M.A a) (fun _ => InhabCalc.combPot Q t 0) j z = chernTop ((∑ i, C (t i) * X (i, 1)) ^ Y.dim) (fun v => lineGram (cxSt F) (fun i => m i (I.ε a)) A (c.e.symm v)) (c.e (c.finChart.symm z)) := by
  first | exact @GlobalTheory.ChernWeilLine.locDens_combPot_eq_chernTop | exact GlobalTheory.ChernWeilLine.locDens_combPot_eq_chernTop | (intros; apply GlobalTheory.ChernWeilLine.locDens_combPot_eq_chernTop <;> assumption)
