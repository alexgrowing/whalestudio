import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationTensorMapInjectiveCokerKilled
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_tensor_map_injective_coker_killed : ∀ (R A B : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B), Function.Injective ψ → ∀ s : R, s ≠ 0 → (∀ b : B, s • b ∈ ψ.range) → Function.Injective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) ∧ algebraMap R (Localization.AtPrime p) s ≠ 0 ∧ ∀ y : Localization.AtPrime p ⊗[R] B, algebraMap R (Localization.AtPrime p) s • y ∈ (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ).range := by
  first | exact @GlobalTheory.localization_map_injective_coker_killed | exact GlobalTheory.localization_map_injective_coker_killed | (intros; apply GlobalTheory.localization_map_injective_coker_killed <;> assumption)
