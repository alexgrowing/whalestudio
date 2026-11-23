import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuativeLiftExistsUnique
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuative_lift_existsUnique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω), CoordTie ℤ ξ x → ∀ (C : Type) [Field C] (V : ValuationSubring C) (zC : Spec (CommRingCat.of C) ⟶ X), genPt ξ ⤳ centre zC → ∃! z : Spec (CommRingCat.of V) ⟶ X, genPt ξ ⤳ centre z ∧ Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z = zC := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coord_point_extends | exact GlobalTheory.CompanionTheory.Ar.coord_point_extends | (intros; apply GlobalTheory.CompanionTheory.Ar.coord_point_extends <;> assumption)
