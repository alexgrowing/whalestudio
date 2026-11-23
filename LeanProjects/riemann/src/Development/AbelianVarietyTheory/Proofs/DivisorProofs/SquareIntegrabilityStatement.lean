import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrability
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
theorem _root_.GlobalTheory.T.square_integrability : GlobalTheory.ThK.KP → GlobalTheory.ThK.SqInt := by
  first | exact @GlobalTheory.ThK.sqInt | exact GlobalTheory.ThK.sqInt | (intros; apply GlobalTheory.ThK.sqInt <;> assumption)
