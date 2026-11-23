import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtCompLocalHom
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valAt_comp_local_hom : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) (a : Ω) (r : R), ValAt ξ z a r → genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) → ValAt ξ (Spec.map (CommRingCat.ofHom ψ) ≫ z) a (ψ r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change | exact GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change | (intros; apply GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change <;> assumption)
