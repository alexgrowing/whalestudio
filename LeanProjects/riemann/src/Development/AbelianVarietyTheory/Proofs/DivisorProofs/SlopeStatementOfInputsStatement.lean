import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeStatementOfInputs
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesY
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
theorem _root_.GlobalTheory.T.slope_statement_of_inputs : GlobalTheory.CovTop.HypothesesXH → HypothesesY → Hypotheses2 → HypothesesH → InputsSt → SlopeSt := by
  first | exact @GlobalTheory.CovHt.SlopeTrue.main | exact GlobalTheory.CovHt.SlopeTrue.main | (intros; apply GlobalTheory.CovHt.SlopeTrue.main <;> assumption)
