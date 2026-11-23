import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliNonemptyPositiveDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_moduli_nonempty_positive_dim : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ∀ l : Level H, ∃ (Xo : Moduli D l) (y : Sp ℂ ⟶ Xo.X), y ≫ Xo.s = spMap (KA l).val.toRingHom ∧ ∃ x : Over.mk y ⟶ Xo.univ.t.G, x ≠ 1) ∧ ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l), 0 < D.dim ∧ Nonempty Xo.X ∧ ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), 0 < g ∧ IsTypeFn H D.p D.q ty ∧ Nonempty (FamilyUnif Xo (KA l).val.toRingHom ty) := by
  first | exact @GlobalTheory.ModuliInhabitant.moduli_inhabited | exact GlobalTheory.ModuliInhabitant.moduli_inhabited | (intros; apply GlobalTheory.ModuliInhabitant.moduli_inhabited <;> assumption)
