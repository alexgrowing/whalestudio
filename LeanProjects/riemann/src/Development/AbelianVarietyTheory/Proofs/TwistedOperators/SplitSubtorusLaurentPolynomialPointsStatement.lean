import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusLaurentPolynomialPoints
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_subtorus_laurentPolynomial_points : GlobalTheory.RegSS.SubtorusLaurent := by
  first | exact @GlobalTheory.RegSS.subtorusLaurent | exact GlobalTheory.RegSS.subtorusLaurent | (intros; apply GlobalTheory.RegSS.subtorusLaurent <;> assumption)
