import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerSplitRankUpperBound
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_splitRank_upper_bound : GlobalTheory.RegSS.SubtorusLaurent → GlobalTheory.RegSS.CharacterMonomial → GlobalTheory.RegSS.SeparatingPoints → GlobalTheory.RegSS.SplitRankUpper := by
  first | exact @GlobalTheory.RegSS.SplitRankBound.splitRankUpper | exact GlobalTheory.RegSS.SplitRankBound.splitRankUpper | (intros; apply GlobalTheory.RegSS.SplitRankBound.splitRankUpper <;> assumption)
