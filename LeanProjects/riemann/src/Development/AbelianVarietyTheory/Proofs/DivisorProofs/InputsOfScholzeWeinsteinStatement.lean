import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InputsOfScholzeWeinstein
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inputs_of_scholze_weinstein : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → Known₂ → GlobalTheory.Published.ScholzeWeinsteinB → InputsSt := by
  first | exact @GlobalTheory.CovHt.inputsSt_of_scholzeWeinstein | exact GlobalTheory.CovHt.inputsSt_of_scholzeWeinstein | (intros; apply GlobalTheory.CovHt.inputsSt_of_scholzeWeinstein <;> assumption)
