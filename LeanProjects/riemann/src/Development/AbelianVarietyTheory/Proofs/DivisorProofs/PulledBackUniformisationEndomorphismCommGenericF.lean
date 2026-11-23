import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsCarryCommonFlagSpectrumMapFieldExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ArcPull

namespace GlobalTheory.Poinc.AComm

theorem pulled_end_comm : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'} (g : R →+* R') (hg : Function.Injective g) {D : DegData R I} {D' : DegData R' I'} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U' : UnifPre I' D' A' ((Over.pullback (specOf g)).obj G)) (gA : A'.A.left ⟶ A.A.left), IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA → gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (specOf g) → ∀ (E : EndU U) (E' : EndU U'), E'.aG = (Over.pullback (specOf g)).map E.aG → E'.aA.left ≫ gA = gA ≫ E.aA.left := by
  intro R R' _ _ _ _ I I' g hg D D' A A' G _ _ U U' gA hgA hfst E E' hE
  have key : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
      {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
      (U : UnifPre I D A G) (E : EndU U) {Z : Scheme.{0}} (h : pullback G.hom (jK R) ⟶ Z),
      E.aA.left ≫ U.gen.inv.left ≫ h = U.gen.inv.left ≫ ((Over.pullback (jK R)).map E.aG).left ≫ h := by
    intro R _ _ I D A G _ _ U E Z h
    have k : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK R)).map E.aG := by
      rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
    have k' := congrArg CommaMorphism.left k
    simp only [Over.comp_left] at k'
    rw [← Category.assoc, k', Category.assoc]
  have pf : ∀ {Y S : Scheme.{0}} (f : Y ⟶ S) {H H' : Over S} (a : H ⟶ H') {Z : Scheme.{0}} (h : H'.left ⟶ Z),
      ((Over.pullback f).map a).left ≫ pullback.fst H'.hom f ≫ h = pullback.fst H.hom f ≫ a.left ≫ h := by
    intro Y S f H H' a Z h
    have e : ((Over.pullback f).map a).left ≫ pullback.fst H'.hom f = pullback.fst H.hom f ≫ a.left :=
      pullback.lift_fst _ _ _
    rw [← Category.assoc, e, Category.assoc]
  have pf0 : ∀ {Y S : Scheme.{0}} (f : Y ⟶ S) {H H' : Over S} (a : H ⟶ H'),
      ((Over.pullback f).map a).left ≫ pullback.fst H'.hom f = pullback.fst H.hom f ≫ a.left :=
    by intro Y S f H H' a; exact pullback.lift_fst _ _ _
  have ws : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
      {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
      (U : UnifPre I D A G), U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := by
    intro R _ _ I D A G _ _ U
    simpa using Over.w U.gen.inv
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have inj : ∀ a b : A'.A.left ⟶ A.A.left, a ≫ U.gen.inv.left = b ≫ U.gen.inv.left → a = b := by
    intro a b h
    have := congrArg (· ≫ U.gen.hom.left) h
    simpa only [Category.assoc, hgi, Category.comp_id] using this
  apply inj
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [hfst, key U' E', pf, hE, pf0, key U E, pf0]
    rw [reassoc_of% hfst]
  · simp only [Category.assoc]
    rw [ws U, Over.w E.aA, hgA.1.w, ← Category.assoc, Over.w E'.aA]

end GlobalTheory.Poinc.AComm
