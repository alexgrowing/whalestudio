import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupGaugeVolumeInHermitianUnitary
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_gaugeVolume_in_hermitianUnitary : PI.RhsWLim.W.GaugeVolUk := by
  first | exact @GlobalTheory.GaugeVolFixer.gaugeVolUk | exact GlobalTheory.GaugeVolFixer.gaugeVolUk | (intros; apply GlobalTheory.GaugeVolFixer.gaugeVolUk <;> assumption)
