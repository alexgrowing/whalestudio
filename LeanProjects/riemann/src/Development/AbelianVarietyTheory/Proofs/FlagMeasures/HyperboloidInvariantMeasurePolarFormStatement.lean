import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasurePolarForm
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvO
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperboloid_invariant_measure_polar_form : PI.RhsWLim.W.RI.HypQ := by
  first | exact @GlobalTheory.HyperboloidPolar.hypQ | exact GlobalTheory.HyperboloidPolar.hypQ | (intros; apply GlobalTheory.HyperboloidPolar.hypQ <;> assumption)
