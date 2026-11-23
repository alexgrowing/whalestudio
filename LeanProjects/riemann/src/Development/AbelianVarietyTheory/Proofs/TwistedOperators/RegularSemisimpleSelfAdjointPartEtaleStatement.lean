import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartEtale
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_selfAdjointPart_etale : GlobalTheory.RegSS.PlusEtale := by
  first | exact @GlobalTheory.RegSS.plusEtale | exact GlobalTheory.RegSS.plusEtale | (intros; apply GlobalTheory.RegSS.plusEtale <;> assumption)
