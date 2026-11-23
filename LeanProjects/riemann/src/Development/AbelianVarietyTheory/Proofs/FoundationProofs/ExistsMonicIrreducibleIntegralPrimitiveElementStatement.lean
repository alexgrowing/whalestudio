import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElement
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_irreducible_integral_primitive_element : ∀ {F : Type} [Field F] [CharZero F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic ∧ Irreducible Φ ∧ Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 ∧ ∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω := by
  first | exact @GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive | exact GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive | (intros; apply GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive <;> assumption)
