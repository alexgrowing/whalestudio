import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgebraicOfEllipticTorsionCoordinatesFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_of_ellipticTorsionCoordinates_finite : ∀ (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (A : WeierstrassCurve F) (n : ℕ), (torsionCoords (A.baseChange ℂ) n).Finite → ∀ z ∈ torsionCoords (A.baseChange ℂ) n, IsAlgebraic ℚ z := by
  first | exact @GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite | exact GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite | (intros; apply GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite <;> assumption)
