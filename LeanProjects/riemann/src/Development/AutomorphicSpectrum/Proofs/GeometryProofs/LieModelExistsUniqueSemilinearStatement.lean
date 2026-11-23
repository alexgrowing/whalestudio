import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_existsUnique_semilinear : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R') (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (spMap c ≫ x) E'), ∃! j : E →ₛₗ[c] E', ∀ e, M.Lifts c (𝟙 G.left) e (M'.pt (j e)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts | exact GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts | (intros; apply GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts <;> assumption)
