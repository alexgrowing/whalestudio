import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTermFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_term_formula : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → OnObj fun D O _ _ _ _ => ∀ c (M : DRBase O c) (R : ℝ), 2 ≤ R → termW O c R = M.val R (genericPoint M.B) (dimGr D.what₂.Tau O.N O.j - 1) / (Module.finrank ℚ D.what₂.LL : ℝ) := by
  first | exact @GlobalTheory.OrthFilt.termW_eq_val | exact GlobalTheory.OrthFilt.termW_eq_val | (intros; apply GlobalTheory.OrthFilt.termW_eq_val <;> assumption)
