import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraMapEqOfFaithfullyFlatIncludeLeftEqI
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] (b : B), (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) b = (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) b → ∃ a : A, algebraMap A B a = b := by
  first | (exact @GlobalTheory.EtC.exists_algebraMap_eq_of_includeLeft_eq_includeRight) | (exact GlobalTheory.EtC.exists_algebraMap_eq_of_includeLeft_eq_includeRight) | (intros; apply GlobalTheory.EtC.exists_algebraMap_eq_of_includeLeft_eq_includeRight  <;> assumption)
