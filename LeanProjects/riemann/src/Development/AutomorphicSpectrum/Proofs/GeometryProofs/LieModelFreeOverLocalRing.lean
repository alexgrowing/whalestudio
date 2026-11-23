import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieFreeSmooth

theorem lieModel_free_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom →
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E]
      [Module R E] (M : LieModel G x E), ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R E) := by
  intro S G _ hG R _ _ x E _ _ M
  haveI := hG
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.lie_model_finite_projective S G R x E M
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R E := Module.free_of_flat_of_isLocalRing
  exact ⟨_, ⟨Module.finBasis R E⟩⟩

end GlobalTheory.CompanionTheory.Ar.LieFreeSmooth
