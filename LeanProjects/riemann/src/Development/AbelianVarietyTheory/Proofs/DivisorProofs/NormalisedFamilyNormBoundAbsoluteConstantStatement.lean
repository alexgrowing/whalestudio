import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNormBoundAbsoluteConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_normBound_absoluteConstant : GlobalTheory.ColNorms.FamilyNorms := by
  first | exact @GlobalTheory.ColNorms.FamilyBound.familyNorms | exact GlobalTheory.ColNorms.FamilyBound.familyNorms | (intros; apply GlobalTheory.ColNorms.FamilyBound.familyNorms <;> assumption)
