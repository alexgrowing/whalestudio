import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SourceStatementOfSlope
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.source_statement_of_slope : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegSt → SlopeSt → SrcSt := by
  first | exact @GlobalTheory.CovHt.Link.srcSt_of_slopeSt | exact GlobalTheory.CovHt.Link.srcSt_of_slopeSt | (intros; apply GlobalTheory.CovHt.Link.srcSt_of_slopeSt <;> assumption)
