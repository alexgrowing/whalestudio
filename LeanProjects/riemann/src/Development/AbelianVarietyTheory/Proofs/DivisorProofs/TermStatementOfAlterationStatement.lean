import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermStatementOfAlteration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
theorem _root_.GlobalTheory.T.term_statement_of_alteration : GlobalTheory.Published.RegularAlteration → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → TermSt := by
  first | exact @GlobalTheory.MixedLocalChains.TermPf.termSt_holds | exact GlobalTheory.MixedLocalChains.TermPf.termSt_holds | (intros; apply GlobalTheory.MixedLocalChains.TermPf.termSt_holds <;> assumption)
