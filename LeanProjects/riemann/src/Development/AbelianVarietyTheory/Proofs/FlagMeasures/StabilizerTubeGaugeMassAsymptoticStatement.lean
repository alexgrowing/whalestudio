import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTubeGaugeMassAsymptotic
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizerTube_gaugeMass_asymptotic : PI.RhsWLim.W.TubeLimK := by
  first | exact @GlobalTheory.StabTube.tubeLimK | exact GlobalTheory.StabTube.tubeLimK | (intros; apply GlobalTheory.StabTube.tubeLimK <;> assumption)
