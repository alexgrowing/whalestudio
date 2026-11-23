import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalFiniteTypeOver
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_finite_type_over : ∀ (A B : Type) [CommRing A] [Algebra.EssFiniteType ℤ A] [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] (C : Subalgebra A B), Algebra.FiniteType A C → (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, s ≠ 0 ∧ s * b = a) → ∃ C' : Subalgebra A B, C ≤ C' ∧ Algebra.FiniteType A C' ∧ IsIntegrallyClosed C' ∧ ∀ x ∈ C', IsIntegral C x := by
  first | exact @GlobalTheory.exists_finiteType_isIntegrallyClosed_integral_over | exact GlobalTheory.exists_finiteType_isIntegrallyClosed_integral_over | (intros; apply GlobalTheory.exists_finiteType_isIntegrallyClosed_integral_over <;> assumption)
