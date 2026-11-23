import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoQuotientPowFreeOverRegularLocalRing
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modDepthGE_two_quotient_pow_free_over_regularLocalRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ≠ 0 → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B] [Nontrivial B] (k : ℕ), 1 ≤ k → ReciprocityTheory.CA.ModDepthGE R (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) 2 := by
  first | (exact @GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing) | (exact GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing) | (intros; apply GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing  <;> assumption)
