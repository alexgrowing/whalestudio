import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackUniformisationCompIdPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDeterminedByDegenerationDataNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullbackUniformisation_comp_id_pullback : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R')
    (D : DegData R I) (D' D'' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre)
    (hid : IsPullDeg (RingHom.id R') D'.toPre D''.toPre)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' A'' : PolAV (Spec (CommRingCat.of (FractionRing R'))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (G' G'' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (bc' : G'' ≅ (Over.pullback (specOf (RingHom.id R'))).obj G')
    (U : Unif I D A G) (U' : Unif I' D' A' G') (U'' : Unif I' D'' A'' G''),
    IsPullUnif φ hD bc U U' → IsPullUnif (RingHom.id R') hid bc' U' U'' →
    ∃ (h : IsPullDeg φ D.toPre D''.toPre) (bc'' : G'' ≅ (Over.pullback (specOf φ)).obj G),
      IsPullUnif φ h bc'' U U'' ∧ (∀ x, h.xe x = hD.xe (hid.xe x)) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) =
        hid.e.hom.left ≫ pullback.fst D'.toPre.P.A.hom (specOf (RingHom.id R')) ≫
          hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) ∧
      bc''.hom.left ≫ pullback.fst G.hom (specOf φ) =
        bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      (IsMonHom bc.hom → IsMonHom bc'.hom → IsMonHom bc''.hom) := by
  first | exact @GlobalTheory.PullUnifId.isPullUnif_comp_id | exact GlobalTheory.PullUnifId.isPullUnif_comp_id | (intros; apply GlobalTheory.PullUnifId.isPullUnif_comp_id <;> assumption)
