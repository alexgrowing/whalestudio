import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortOfInputs
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_of_inputs : Hypotheses2 → DeepGood → Size → FlatDeg → Short := by
  first | exact @GlobalTheory.CovHt.ShortPf.short | exact GlobalTheory.CovHt.ShortPf.short | (intros; apply GlobalTheory.CovHt.ShortPf.short <;> assumption)
