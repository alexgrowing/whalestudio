import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAtPrimeLocalizationTensor
import Mathlib
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularLocalRing_localization_atPrime_tensor_field : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (r : ℕ) (𝔪 : Ideal (MvPolynomial (Fin r) k)) [𝔪.IsPrime] (𝔫 : Ideal (Localization.AtPrime 𝔪 ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  first | exact @GlobalTheory.isRegularLocalRing_atPrime_localization_tensor | exact GlobalTheory.isRegularLocalRing_atPrime_localization_tensor | (intros; apply GlobalTheory.isRegularLocalRing_atPrime_localization_tensor <;> assumption)
