import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_stabilizer_exists : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.StabEx := by
  first | exact @GlobalTheory.StabHaar.stabEx | exact GlobalTheory.StabHaar.stabEx | (intros; apply GlobalTheory.StabHaar.stabEx <;> assumption)
