import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveElementCoordinatePolynomials
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_element_coordinate_polynomials : ∀ (k C : Type) [Field k] [Field C] [Algebra k C] (d m : ℕ) (t : Fin d → C) (θ : C) (x : Fin m → C), IsAlgebraic (IntermediateField.adjoin k (Set.range t)) θ → (∀ j, x j ∈ IntermediateField.adjoin (IntermediateField.adjoin k (Set.range t)) {θ}) → ∃ (Δ : MvPolynomial (Fin d) k) (Q : Fin m → Polynomial (MvPolynomial (Fin d) k)), MvPolynomial.aeval t Δ ≠ 0 ∧ ∀ j, Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) = MvPolynomial.aeval t Δ * x j := by
  first | exact @GlobalTheory.commonDenominator | exact GlobalTheory.commonDenominator | (intros; apply GlobalTheory.commonDenominator <;> assumption)
