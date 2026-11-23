import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoethe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsFractionRing (rA k x I) F ∧ IsNoetherianRing (rA k x I) := by
  first | (exact @GlobalTheory.PD.rA_isFractionRing_isNoetherianRing) | (exact GlobalTheory.PD.rA_isFractionRing_isNoetherianRing) | (intros; apply GlobalTheory.PD.rA_isFractionRing_isNoetherianRing  <;> assumption)
