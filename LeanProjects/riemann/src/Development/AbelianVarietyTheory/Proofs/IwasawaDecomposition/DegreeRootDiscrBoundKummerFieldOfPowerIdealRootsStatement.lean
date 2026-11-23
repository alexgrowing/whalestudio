import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeRootDiscrBoundKummerFieldOfPowerIdealRoots
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeRootDiscrBound_kummerFieldOfPowerIdealRoots : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ), 0 < h → Sz (kummerField φ h) (Real.log (Module.finrank ℚ E) + ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))) := by
  first | exact @GlobalTheory.FieldSize.sz_kummerField | exact GlobalTheory.FieldSize.sz_kummerField | (intros; apply GlobalTheory.FieldSize.sz_kummerField <;> assumption)
