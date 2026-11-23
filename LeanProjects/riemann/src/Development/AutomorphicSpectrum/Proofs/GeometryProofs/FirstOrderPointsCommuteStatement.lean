import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FirstOrderPointsCommute
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_order_points_commute : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (B : Type) [CommRing B] [IsLocalRing B] (b : Sp B ⟶ S) (A : Type) [CommRing A] (g : B →+* A) (J : Ideal A), J ^ 2 = ⊥ → ∀ x y : Over.mk (spMap g ≫ b) ⟶ G, spMap (Ideal.Quotient.mk J) ≫ x.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → spMap (Ideal.Quotient.mk J) ≫ y.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → ∀ (V : G.left.Opens) (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V) (hxy : ⊤ ≤ (x * y).left ⁻¹ᵁ V) (h1 : ⊤ ≤ (1 : Over.mk (spMap g ≫ b) ⟶ G).left ⁻¹ᵁ V) (f : Γ(G.left, V)), ((x * y).left.appLE V ⊤ hxy).hom f + ((1 : Over.mk (spMap g ≫ b) ⟶ G).left.appLE V ⊤ h1).hom f = (x.left.appLE V ⊤ hx).hom f + (y.left.appLE V ⊤ hy).hom f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.sqzero_add | exact GlobalTheory.CompanionTheory.Ar.sqzero_add | (intros; apply GlobalTheory.CompanionTheory.Ar.sqzero_add <;> assumption)
