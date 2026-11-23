import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEThreeOfFreeRegularLocal
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modDepthGE_three_of_free_regularLocal : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M] [Nontrivial M], ReciprocityTheory.CA.ModDepthGE R M 3 := by
  first | exact @GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing | exact GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing | (intros; apply GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing <;> assumption)
