import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsFifthEstimate
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_gap_bound' : RankGapBound := by
  first | exact @GlobalTheory.BigTop.Fun.ramified_sums_fifth_bound | exact GlobalTheory.BigTop.Fun.ramified_sums_fifth_bound | (intros; apply GlobalTheory.BigTop.Fun.ramified_sums_fifth_bound <;> assumption)
