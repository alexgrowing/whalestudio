import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionLiftIsClosedImmersion
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_lift_is_closed_immersion : ∀ {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsSeparated G.hom] (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ) (i : Γ.G.left ⟶ G.left) (h : Γ.IsTorsionAlong G x N i), IsClosedImmersion (pullback.lift i Γ.G.hom h.isOver : Γ.G.left ⟶ pullback G.hom x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isClosedImmersion_torsion_lift | exact GlobalTheory.CompanionTheory.Ar.BT.isClosedImmersion_torsion_lift | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isClosedImmersion_torsion_lift <;> assumption)
