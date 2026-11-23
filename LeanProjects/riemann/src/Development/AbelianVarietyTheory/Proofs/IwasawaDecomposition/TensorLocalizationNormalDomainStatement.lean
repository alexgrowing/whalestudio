import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorLocalizationNormalDomain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_localization_normal_domain : ∀ (A B D R : Type) [CommRing A] [CommRing B] [CommRing D] [CommRing R] [Algebra A B] [Algebra A D] [Algebra A R] (ι : D →ₐ[A] B), Function.Injective ι → (∀ b, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a) → ∀ (Q : Ideal (B ⊗[A] R)) [Q.IsPrime] (q : Ideal (D ⊗[A] R)) [q.IsPrime], Q.comap (Algebra.TensorProduct.map ι (AlgHom.id A R)) ≤ q → IsDomain (Localization.AtPrime q) → IsIntegrallyClosed (Localization.AtPrime q) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.normal_atPrime_tensor_of_chart_localization | exact GlobalTheory.normal_atPrime_tensor_of_chart_localization | (intros; apply GlobalTheory.normal_atPrime_tensor_of_chart_localization <;> assumption)
