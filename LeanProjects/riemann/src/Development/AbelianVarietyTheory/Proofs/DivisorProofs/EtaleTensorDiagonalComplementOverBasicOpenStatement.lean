import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTensorDiagonalComplementOverBasicOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_tensor_diagonal_complement_over_basicOpen : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∃ e u : A' ⊗[A] A', (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) ∧ algebraMap A (A' ⊗[A] A') f * u = 1 - e := by
  first | (exact @GlobalTheory.etale_diag_complement) | (exact GlobalTheory.etale_diag_complement) | (intros; apply GlobalTheory.etale_diag_complement  <;> assumption)
