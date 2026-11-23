import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ReadInjective : GlobalTheory.BigOn.Exp.ReadInj := by
  first | exact @GlobalTheory.BigOn.Exp.readInj | exact GlobalTheory.BigOn.Exp.readInj | (intros; apply GlobalTheory.BigOn.Exp.readInj <;> assumption)
