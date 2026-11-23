import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroCone
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_evaluation_zero_cone : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.EvZero ∧ GlobalTheory.ThK.EvCone := by
  first | exact @GlobalTheory.ThK.EvMaps.evZero_evCone | exact GlobalTheory.ThK.EvMaps.evZero_evCone | (intros; apply GlobalTheory.ThK.EvMaps.evZero_evCone <;> assumption)
