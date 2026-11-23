import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeMaximalIdeal
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_of_le_maximalIdeal' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (I : Ideal R), I ≤ maximalIdeal R → IsAdicComplete I R := by
  first | exact @GlobalTheory.isAdicComplete_of_le_maximalIdeal | exact GlobalTheory.isAdicComplete_of_le_maximalIdeal | (intros; apply GlobalTheory.isAdicComplete_of_le_maximalIdeal <;> assumption)
