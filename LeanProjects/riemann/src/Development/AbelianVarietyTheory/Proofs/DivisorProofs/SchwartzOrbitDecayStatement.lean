import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecay
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_orbit_decay : GlobalTheory.ThK.KP → GlobalTheory.ThK.SoDecay := by
  first | exact @GlobalTheory.ThKSoDecay.soDecay | exact GlobalTheory.ThKSoDecay.soDecay | (intros; apply GlobalTheory.ThKSoDecay.soDecay <;> assumption)
