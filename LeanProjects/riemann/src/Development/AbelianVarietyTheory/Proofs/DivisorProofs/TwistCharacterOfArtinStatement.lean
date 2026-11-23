import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtin
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_character_of_artin : GlobalTheory.Published.GlobalArtinReciprocity → TwAdm → TwChr := by
  first | exact @GlobalTheory.TwistChr.twChr_of_twAdm | exact GlobalTheory.TwistChr.twChr_of_twAdm | (intros; apply GlobalTheory.TwistChr.twChr_of_twAdm <;> assumption)
