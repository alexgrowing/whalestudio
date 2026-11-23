import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTensorPowers
import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalisation_tensorPowers : Formalism.L2.AlgTh.LocNormPow := by
  first | exact @GlobalTheory.locNormPow_tensorPowers | exact GlobalTheory.locNormPow_tensorPowers | (intros; apply GlobalTheory.locNormPow_tensorPowers <;> assumption)
