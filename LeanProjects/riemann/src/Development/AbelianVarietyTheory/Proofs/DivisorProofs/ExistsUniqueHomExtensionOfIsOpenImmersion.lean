import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SemiAbExtDomain

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

theorem existsUnique_hom_extension_generic (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶ (Over.pullback (spMap (algebraMap R K))).obj H)
    [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f :=
  GlobalTheory.semiAbelianHomExtension_holds.fractionField R K G H hG hH f

theorem existsUnique_iso_extension_generic (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ (Over.pullback (spMap (algebraMap R K))).obj H)
    [IsMonHom e.hom] :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ (Over.pullback (spMap (algebraMap R K))).map E.hom = e.hom :=
  GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso (GlobalTheory.IsNormalScheme.pred _)
    (.fractionField R K) hG hH e

end GlobalTheory.SemiAbExtDomain
