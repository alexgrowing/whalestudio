import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_action_exists : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ActsEx := by
  first | exact @GlobalTheory.ThK.LocalOps.actsEx | exact GlobalTheory.ThK.LocalOps.actsEx | (intros; apply GlobalTheory.ThK.LocalOps.actsEx <;> assumption)
