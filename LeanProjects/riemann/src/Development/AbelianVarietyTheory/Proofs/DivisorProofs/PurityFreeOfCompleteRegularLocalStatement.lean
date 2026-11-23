import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFreeOfCompleteRegularLocal
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.purityFree_of_complete_regularLocal : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], (∀ (S : Type) [CommRing S] [IsRegularLocalRing S], IsAdicComplete (maximalIdeal S) S → ringKrullDim S = ringKrullDim R → GlobalTheory.PurityFree S) → GlobalTheory.PurityFree R := by
  first | exact @GlobalTheory.PurityStep.purityFree_of_complete | exact GlobalTheory.PurityStep.purityFree_of_complete | (intros; apply GlobalTheory.PurityStep.purityFree_of_complete <;> assumption)
