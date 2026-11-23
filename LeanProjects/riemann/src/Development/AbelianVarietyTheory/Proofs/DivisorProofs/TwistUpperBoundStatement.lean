import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistUpperBound
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_upper_bound : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → TwAdm → TwChr → TwLe := by
  first | exact @GlobalTheory.BigOn.Exp.TupLe.twLe | exact GlobalTheory.BigOn.Exp.TupLe.twLe | (intros; apply GlobalTheory.BigOn.Exp.TupLe.twLe <;> assumption)
