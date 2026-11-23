import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_model_base_change : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ X) (V : Type) [AddCommGroup V] [Module R V] (M : LieModel G x V), ∃ (T : Type) (_ : AddCommGroup T) (_ : Module R' T) (_ : Module R T) (_ : IsScalarTower R R' T) (M' : LieModel G (spMap (algebraMap R R') ≫ x) T) (j : V →ₗ[R] T), (∀ e, M.Lifts (algebraMap R R') (𝟙 G.left) e (M'.pt (j e))) ∧ IsBaseChange R' j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange | exact GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange <;> assumption)
