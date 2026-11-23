import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetSurjectiveOfLevi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_surjective_of_levi : LeviExists → CosetSurj := by
  first | exact @GlobalTheory.CompanionTheory.InertCoset.cosetSurj | exact GlobalTheory.CompanionTheory.InertCoset.cosetSurj | (intros; apply GlobalTheory.CompanionTheory.InertCoset.cosetSurj <;> assumption)
