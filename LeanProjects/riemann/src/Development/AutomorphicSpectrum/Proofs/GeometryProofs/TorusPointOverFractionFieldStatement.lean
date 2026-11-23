import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_point_over_fraction_field : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Ω : Type) [Field Ω] (k : FractionRing R →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ Γ.G.left), y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) → ∃ t, y = Spec.map (CommRingCat.ofHom k) ≫ (Γ.pt t).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_eq_comp_pt | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_eq_comp_pt | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_eq_comp_pt <;> assumption)
