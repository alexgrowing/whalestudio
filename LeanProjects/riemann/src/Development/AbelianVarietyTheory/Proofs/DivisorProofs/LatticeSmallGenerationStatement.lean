import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.LatticeSmallGeneration : GlobalTheory.BigOn.Exp.LatSmallGen := by
  first | exact @GlobalTheory.BigOn.Exp.latSmallGen | exact GlobalTheory.BigOn.Exp.latSmallGen | (intros; apply GlobalTheory.BigOn.Exp.latSmallGen <;> assumption)
