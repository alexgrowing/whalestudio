import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorDomainBirational
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_domain_birational : ∀ (A B R : Type) [CommRing A] [CommRing B] [IsDomain B] [CommRing R] [IsDomain R] [Algebra A B] [Algebra A R] [Module.Flat A R], Function.Injective (algebraMap A B) → (∀ b : B, ∃ a s : A, algebraMap A B s ≠ 0 ∧ algebraMap A B s * b = algebraMap A B a) → IsDomain (TensorProduct A B R) ∧ Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by
  first | exact @GlobalTheory.flat_baseChange_birational_isDomain_and_includeRight_injective | exact GlobalTheory.flat_baseChange_birational_isDomain_and_includeRight_injective | (intros; apply GlobalTheory.flat_baseChange_birational_isDomain_and_includeRight_injective <;> assumption)
