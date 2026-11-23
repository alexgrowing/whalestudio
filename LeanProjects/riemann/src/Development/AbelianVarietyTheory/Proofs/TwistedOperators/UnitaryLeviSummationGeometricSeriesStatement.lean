import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLeviSummationGeometricSeries
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_levi_summation_geometric_series : Step := by
  first | exact @GlobalTheory.InertZeta.step | exact GlobalTheory.InertZeta.step | (intros; apply GlobalTheory.InertZeta.step <;> assumption)
