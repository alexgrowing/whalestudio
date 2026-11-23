import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupTangentLift
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_group_tangent_lift : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (p : Ideal R) [p.IsPrime],
  ∃ f : R, f ∉ p ∧ ∃ (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_ : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V),
    RingHom.Smooth (G.hom.appLE V U hUV).hom ∧
    ∃ u : Γ(G.left, U) →+* Localization.Away f,
      (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chart.exists_chart_at_point | exact GlobalTheory.CompanionTheory.Ar.Chart.exists_chart_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Chart.exists_chart_at_point <;> assumption)
