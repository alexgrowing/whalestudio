import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallConstantTermCone
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_constant_term_cone : GlobalTheory.ThK.KP → GlobalTheory.ThK.CTSmallCone := by
  first | exact @GlobalTheory.ConeSmall.ctSmallCone | exact GlobalTheory.ConeSmall.ctSmallCone | (intros; apply GlobalTheory.ConeSmall.ctSmallCone <;> assumption)
