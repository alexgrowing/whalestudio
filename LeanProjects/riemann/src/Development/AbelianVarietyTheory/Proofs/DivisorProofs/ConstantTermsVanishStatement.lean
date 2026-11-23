import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermsVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_terms_vanish : GlobalTheory.ThK.KP → GlobalTheory.ThK.CTBigZero ∧ GlobalTheory.ThK.CTSmallZero := by
  first | exact @GlobalTheory.ThKCtZero.ctZero | exact GlobalTheory.ThKCtZero.ctZero | (intros; apply GlobalTheory.ThKCtZero.ctZero <;> assumption)
