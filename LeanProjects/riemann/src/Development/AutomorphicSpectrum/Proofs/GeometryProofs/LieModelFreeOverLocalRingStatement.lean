import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRing
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_free_over_local_ring : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R E) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth | exact GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth <;> assumption)
