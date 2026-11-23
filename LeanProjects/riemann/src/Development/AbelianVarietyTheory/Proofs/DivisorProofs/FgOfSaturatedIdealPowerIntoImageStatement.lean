import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgOfSaturatedIdealPowerIntoImage
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fg_of_ideal_pow_smul_mem_range_tensor : ∀ (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] (I : Ideal S), (∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ I ^ k, IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c) → ∀ (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M] (N : Submodule S (FractionRing S ⊗[S] M)), (∀ z ∈ N, ∃ k : ℕ, ∀ a ∈ I ^ k, a • z ∈ LinearMap.range (TensorProduct.mk S (FractionRing S) M 1)) → N.FG := by
  first | exact @GlobalTheory.fg_of_saturated_ideal_power_into_image | exact GlobalTheory.fg_of_saturated_ideal_power_into_image | (intros; apply GlobalTheory.fg_of_saturated_ideal_power_into_image <;> assumption)
