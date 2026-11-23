import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairStatementOfHeightAlteration
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VdivLnIdFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration

theorem _root_.GlobalTheory.T.pair_statement_of_height_alteration : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.PairTerm.PairSt := by
  first | exact @GlobalTheory.PairTerm.pairSt | exact GlobalTheory.PairTerm.pairSt | (intros; apply GlobalTheory.PairTerm.pairSt <;> assumption)
