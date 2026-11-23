import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatchingExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matching_exists : GlobalTheory.ThK.KP → GlobalTheory.ThK.MatchEx := by
  first | exact @GlobalTheory.ThK.matchEx_of_classicalTheorems | exact GlobalTheory.ThK.matchEx_of_classicalTheorems | (intros; apply GlobalTheory.ThK.matchEx_of_classicalTheorems <;> assumption)
