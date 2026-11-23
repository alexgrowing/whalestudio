import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem eigSp_comp_ringEquiv : ∀ (R E O : Type) [CommRing R] [AddCommGroup E] [Module R E] [CommRing O] (ρ : O →+* Module.End R E) (s : O ≃+* O) (τ : O →+* R), eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ := by
  intro R E O _ _ _ _ ρ s τ
  unfold eigSp
  exact s.surjective.iInf_comp (fun b => LinearMap.ker (ρ b - τ b • LinearMap.id))

end GlobalTheory.CompanionTheory.Ar
