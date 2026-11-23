import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialPrimitiveOverBasis
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monic_polynomial_primitive_over_basis : ∀ (k C : Type) [Field k] [Field C] [Algebra k C] (d : ℕ) (t : Fin d → C) (α : C), AlgebraicIndependent k t → IsAlgebraic (IntermediateField.adjoin k (Set.range t)) α → ∃ (θ : C) (P : Polynomial (MvPolynomial (Fin d) k)), P.Monic ∧ Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ P = 0 ∧ IsAlgebraic (IntermediateField.adjoin k (Set.range t)) θ ∧ α ∈ IntermediateField.adjoin (IntermediateField.adjoin k (Set.range t)) {θ} ∧ ∀ R : Polynomial (MvPolynomial (Fin d) k), Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ R = 0 → P ∣ R := by
  first | exact @GlobalTheory.exists_monic_integral_primitive_multiple | exact GlobalTheory.exists_monic_integral_primitive_multiple | (intros; apply GlobalTheory.exists_monic_integral_primitive_multiple <;> assumption)
