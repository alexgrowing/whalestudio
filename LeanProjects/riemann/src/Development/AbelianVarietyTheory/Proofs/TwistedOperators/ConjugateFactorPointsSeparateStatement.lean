import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateFactorPointsSeparate
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_factor_points_separate : GlobalTheory.RegSS.SeparatingPoints := by
  first | exact @GlobalTheory.RegSS.separatingPoints | exact GlobalTheory.RegSS.separatingPoints | (intros; apply GlobalTheory.RegSS.separatingPoints <;> assumption)
