import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_eq_tensorPower_vacuum : GlobalTheory.ColNorms.FamilyTie := by
  first | exact @GlobalTheory.FamilyTieProof.familyTie | exact GlobalTheory.FamilyTieProof.familyTie | (intros; apply GlobalTheory.FamilyTieProof.familyTie <;> assumption)
