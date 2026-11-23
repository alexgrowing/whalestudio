import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedUniformisedGroupPointExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValTorusPointAndTranslate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickenedUniformisedGroup_point_ext : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left), r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom → r ≫ g.pG.left = r' ≫ g.pG.left → (∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ χ : D.X, val (g.t χ) r z J = val (g.t χ) r' z J) → r = r' := by
  first | exact @GlobalTheory.Mum.gtCoord_point_ext | exact GlobalTheory.Mum.gtCoord_point_ext | (intros; apply GlobalTheory.Mum.gtCoord_point_ext <;> assumption)
