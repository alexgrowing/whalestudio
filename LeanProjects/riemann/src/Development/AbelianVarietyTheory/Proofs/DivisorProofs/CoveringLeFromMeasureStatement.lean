import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringLeFromMeasure
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_le_from_measure : Gram → Meas → GlobalTheory.CovTop.Rat → CoreLe := by
  first | exact @GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat | exact GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat | (intros; apply GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat <;> assumption)
