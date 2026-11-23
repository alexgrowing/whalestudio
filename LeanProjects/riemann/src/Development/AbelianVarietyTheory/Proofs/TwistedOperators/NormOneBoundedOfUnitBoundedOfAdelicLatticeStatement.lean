import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneBoundedOfUnitBoundedOfAdelicLattice
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOfUnitBounded_of_tensorLattice' : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.NormOfUnitBounded := by
  first | exact @GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice | exact GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice | (intros; apply GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice <;> assumption)
