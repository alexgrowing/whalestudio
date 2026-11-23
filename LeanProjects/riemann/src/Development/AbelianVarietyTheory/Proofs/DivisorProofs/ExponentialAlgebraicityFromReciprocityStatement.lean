import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialAlgebraicityFromReciprocity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRootOfExp
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_algebraicity_from_reciprocity : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → GlobalTheory.BigOn.Exp.ExpAlg := by
  first | exact @GlobalTheory.BigOn.Exp.expAlg | exact GlobalTheory.BigOn.Exp.expAlg | (intros; apply GlobalTheory.BigOn.Exp.expAlg <;> assumption)
