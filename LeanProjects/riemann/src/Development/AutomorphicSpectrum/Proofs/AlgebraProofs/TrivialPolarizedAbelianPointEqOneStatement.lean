import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialPolarizedAbelianPointEqOne
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_polarized_abelian_point_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (P : Out.PolAV (Spec (CommRingCat.of R))), P.g = 0 → ∀ z : sp (R₀ := R) R ⟶ P.A, z = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero | exact GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero <;> assumption)
