import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleTensorQuadraticSplitAlgClosed
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_tensor_quadratic_split_algClosed : GlobalTheory.RegSS.SplitClosed := by
  first | exact @GlobalTheory.RegSS.splitClosed | exact GlobalTheory.RegSS.splitClosed | (intros; apply GlobalTheory.RegSS.splitClosed <;> assumption)
