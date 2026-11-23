import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegerOfMaximalIdealPowSmulIsInteger
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInteger_of_maximalIdeal_pow_smul_isInteger' : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S → ∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ maximalIdeal S ^ k, IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c := by
  first | exact @GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger | exact GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger | (intros; apply GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger <;> assumption)
