import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaModelCoefficientsInvertL
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_model_coefficients_invert_l : Formalism.L2.KerInert.BeCob.BeCoef := by
  first | exact @GlobalTheory.BeCoefficients.beCoef | exact GlobalTheory.BeCoefficients.beCoef | (intros; apply GlobalTheory.BeCoefficients.beCoef <;> assumption)
