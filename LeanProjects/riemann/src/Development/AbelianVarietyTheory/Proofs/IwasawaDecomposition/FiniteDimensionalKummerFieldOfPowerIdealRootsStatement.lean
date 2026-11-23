import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKummerFieldOfPowerIdealRoots
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_kummerFieldOfPowerIdealRoots : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ), h ≠ 0 → FiniteDimensional ℚ (kummerField φ h) := by
  first | exact @GlobalTheory.Mem.FieldsEx.finiteDimensional_kummerField | exact GlobalTheory.Mem.FieldsEx.finiteDimensional_kummerField | (intros; apply GlobalTheory.Mem.FieldsEx.finiteDimensional_kummerField <;> assumption)
