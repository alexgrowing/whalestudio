import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameFormOfLeviCombination
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_form_of_levi_combination : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {ι : Type} [Fintype ι] (P : LocPot X) (Q : ι → LocPot X) (t : ι → ℝ), (∀ i, IsPotential A (Q i)) → (∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A P j y w = ∑ i, t i * leviAt A (Q i) j y w) → GlobalTheory.SameForm A P (InhabCalc.combPot Q t 0) := by
  first | exact @GlobalTheory.ChernWeilLine.sameForm_combPot_of_levi | exact GlobalTheory.ChernWeilLine.sameForm_combPot_of_levi | (intros; apply GlobalTheory.ChernWeilLine.sameForm_combPot_of_levi <;> assumption)
