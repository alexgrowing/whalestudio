import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtComp
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twAdm' : TwAdm := by
  first | exact @GlobalTheory.BigOn.Exp.twAdm | exact GlobalTheory.BigOn.Exp.twAdm | (intros; apply GlobalTheory.BigOn.Exp.twAdm <;> assumption)
