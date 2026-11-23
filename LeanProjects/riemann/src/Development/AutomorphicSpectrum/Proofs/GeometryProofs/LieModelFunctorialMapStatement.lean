import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_functorial_map : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (M' : LieModel G' x E') (f : G ⟶ G') [IsMonHom f], ∃! A : E →ₗ[R] E', ∀ e, M'.pt (A e) = M.pt e ≫ f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff | exact GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff <;> assumption)
