import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeExistenceOfDvrLiftsLocallyNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankMumfordBundleCechHomologyOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalk
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.EndLoc.HomFixProper

theorem lbIso_pull_eq {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {f g : Y ⟶ X} (h : f = g) :
    LBIso (L.pull f) (L.pull g) := h ▸ GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL f)

theorem lbIso_pull_pull {X Y : Scheme.{0}} {L L' : LB X} (h : LBIso L L') (f : Y ⟶ X) :
    LBIso (L.pull f) (L'.pull f) :=
  LBIso.chartPull (chartPullPull L f) (chartPullPull L' f) h

macro "lbt" : tactic => `(tactic| (repeat (first | assumption | apply pull_isLB)))

theorem isProper_of_finiteType : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → QuasiCompact R.π → IsSeparated R.π → LocallyOfFiniteType R.π → IsProper R.π := by
  intro S _ A B _ _ _ _ L M R hA hB hL hM _ _ hqc hsep hlft
  have hex : ValuativeCriterion.Existence R.π := by
    refine GlobalTheory.T.valuativeExistence_of_dvr_lifts_locallyNoetherian R.π hlft hqc hsep fun V _ _ _ x y hxy => ?_
    haveI := R.hom

    let AV := (Over.pullback y).obj A
    let ψA : AV.left ⟶ A.left := pullback.fst A.hom y
    have hVA : IsGrpPullback AV A y ψA := isGrpPullback_pullback A y
    have hAV : IsAbelianScheme AV := GlobalTheory.isAbelianScheme_pullback_obj y A hA
    let BV := (Over.pullback y).obj B
    let ψB : BV.left ⟶ B.left := pullback.fst B.hom y
    have hVB : IsGrpPullback BV B y ψB := isGrpPullback_pullback B y
    have hBV : IsAbelianScheme BV := GlobalTheory.isAbelianScheme_pullback_obj y B hB

    let AK := (Over.pullback x).obj R.AH
    let pA : AK.left ⟶ R.AH.left := pullback.fst R.AH.hom x
    have hK1A : IsGrpPullback AK R.AH x pA := isGrpPullback_pullback R.AH x
    have hKA : IsGrpPullback AK A (x ≫ R.π) (pA ≫ R.φA) := hK1A.comp R.pbA
    have hKA' : IsGrpPullback AK A (Out.jK V ≫ y) (pA ≫ R.φA) := hKA.congr hxy rfl
    let BK := (Over.pullback x).obj R.BH
    let pB : BK.left ⟶ R.BH.left := pullback.fst R.BH.hom x
    have hK1B : IsGrpPullback BK R.BH x pB := isGrpPullback_pullback R.BH x
    have hKB : IsGrpPullback BK B (x ≫ R.π) (pB ≫ R.φB) := hK1B.comp R.pbB
    have hKB' : IsGrpPullback BK B (Out.jK V ≫ y) (pB ≫ R.φB) := hKB.congr hxy rfl
    let κA : AK.left ⟶ AV.left := hVA.1.lift (pA ≫ R.φA) (AK.hom ≫ Out.jK V)
      ((Category.assoc _ _ _).symm.trans (hKA'.1.w.trans (Category.assoc _ _ _).symm))
    have hκA1 : κA ≫ ψA = pA ≫ R.φA := hVA.1.lift_fst _ _ _
    have hκA2 : κA ≫ AV.hom = AK.hom ≫ Out.jK V := hVA.1.lift_snd _ _ _
    have hκA : IsGrpPullback AK AV (Out.jK V) κA := IsGrpPullback.cancel hVA (hKA'.congr rfl hκA1.symm) hκA2
    let κB : BK.left ⟶ BV.left := hVB.1.lift (pB ≫ R.φB) (BK.hom ≫ Out.jK V)
      ((Category.assoc _ _ _).symm.trans (hKB'.1.w.trans (Category.assoc _ _ _).symm))
    have hκB1 : κB ≫ ψB = pB ≫ R.φB := hVB.1.lift_fst _ _ _
    have hκB2 : κB ≫ BV.hom = BK.hom ≫ Out.jK V := hVB.1.lift_snd _ _ _
    have hκB : IsGrpPullback BK BV (Out.jK V) κB := IsGrpPullback.cancel hVB (hKB'.congr rfl hκB1.symm) hκB2

    let ΦK : AK ⟶ BK := (Over.pullback x).map R.Φ
    have hΦK : IsMonHom ΦK := inferInstance
    have hΦK1 : ΦK.left ≫ pB = pA ≫ R.Φ.left := pullback.lift_fst _ _ _
    obtain ⟨ΦV, hΦV, hΦV1, -⟩ := GlobalTheory.abelianScheme_hom_extends_dedekind_of_isGrpPullback
      GlobalTheory.homExtension_semiAbelian_dvr V (FractionRing V) AV BV AK BK κA κB hAV hBV hκA hκB ΦK hΦK

    have iso : LBIso (L.pull ψA) ((M.pull ψB).pull ΦV.left) := by
      have hS := GlobalTheory.isSemiAbelian_of_isAbelianScheme AV hAV
      refine GlobalTheory.Poinc.Eq8.StalkPow.lbIso_of_generic_fibre V AV hS _ _ (pull_isLB hL _)
        (pull_isLB (pull_isLB hM _) _) ?_
      have P := hκA.1
      have e : pullback.fst AV.hom (Out.jK V) = P.isoPullback.inv ≫ κA := by simp
      rw [e]
      set u := P.isoPullback.inv
      have i0 := lbIso_pull_pull R.iso (u ≫ pA)
      have hm := pull_isLB hM R.φB
      have eqM : ((u ≫ pA) ≫ R.Φ.left) ≫ R.φB = ((u ≫ κA) ≫ ΦV.left) ≫ ψB := by
        calc ((u ≫ pA) ≫ R.Φ.left) ≫ R.φB = u ≫ (ΦK.left ≫ pB) ≫ R.φB := by
                rw [hΦK1]; simp only [Category.assoc]
            _ = u ≫ ΦK.left ≫ κB ≫ ψB := by rw [hκB1]; simp only [Category.assoc]
            _ = ((u ≫ κA) ≫ ΦV.left) ≫ ψB := by
                rw [← Category.assoc ΦK.left, hΦV1]; simp only [Category.assoc]
      refine LBIso.trans (B := L.pull ((u ≫ κA) ≫ ψA)) (by lbt) (by lbt) (by lbt)
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL _ _) ?_
      refine LBIso.trans (B := L.pull ((u ≫ pA) ≫ R.φA)) (by lbt) (by lbt) (by lbt)
        (lbIso_pull_eq hL (by simp only [Category.assoc, hκA1])) ?_
      refine LBIso.trans (B := (L.pull R.φA).pull (u ≫ pA)) (by lbt) (by lbt) (by lbt)
        (LBIso.symm (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL _ _)) ?_
      refine LBIso.trans (B := ((M.pull R.φB).pull R.Φ.left).pull (u ≫ pA)) (by lbt) (by lbt) (by lbt) i0 ?_
      refine LBIso.trans (B := (M.pull R.φB).pull ((u ≫ pA) ≫ R.Φ.left)) (by lbt) (by lbt) (by lbt)
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hm _ _) ?_
      refine LBIso.trans (B := M.pull (((u ≫ pA) ≫ R.Φ.left) ≫ R.φB)) (by lbt) (by lbt) (by lbt)
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _) ?_
      refine LBIso.trans (B := M.pull (((u ≫ κA) ≫ ΦV.left) ≫ ψB)) (by lbt) (by lbt) (by lbt)
        (lbIso_pull_eq hM eqM) ?_
      refine LBIso.symm (LBIso.trans (B := (M.pull ψB).pull ((u ≫ κA) ≫ ΦV.left)) (by lbt) (by lbt) (by lbt)
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp (pull_isLB hM _) _ _) ?_)
      exact GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _

    obtain ⟨g, ⟨hg, χA, χB, hχA, hχB, hχA1, hχB1, hχΦ⟩, -⟩ :=
      R.rep (Sp V) y AV BV ψA ψB ΦV hVA hVB hΦV iso
    have isoK : LBIso (L.pull (pA ≫ R.φA)) ((M.pull (pB ≫ R.φB)).pull ΦK.left) := by
      have hm := pull_isLB hM R.φB
      refine LBIso.trans (B := (L.pull R.φA).pull pA) (by lbt) (by lbt) (by lbt)
        (LBIso.symm (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL _ _)) ?_
      refine LBIso.trans (B := ((M.pull R.φB).pull R.Φ.left).pull pA) (by lbt) (by lbt) (by lbt)
        (lbIso_pull_pull R.iso pA) ?_
      refine LBIso.trans (B := (M.pull R.φB).pull (pA ≫ R.Φ.left)) (by lbt) (by lbt) (by lbt)
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hm _ _) ?_
      refine LBIso.trans (B := M.pull ((pA ≫ R.Φ.left) ≫ R.φB)) (by lbt) (by lbt) (by lbt)
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _) ?_
      refine LBIso.trans (B := M.pull (ΦK.left ≫ pB ≫ R.φB)) (by lbt) (by lbt) (by lbt)
        (lbIso_pull_eq hM (by rw [← Category.assoc, hΦK1])) ?_
      exact LBIso.symm (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _)
    obtain ⟨g0, -, huniq⟩ := R.rep (Sp (FractionRing V)) (x ≫ R.π) AK BK (pA ≫ R.φA) (pB ≫ R.φB) ΦK hKA hKB hΦK isoK
    have e1 : x = g0 := huniq x ⟨rfl, pA, pB, hK1A, hK1B, rfl, rfl, hΦK1⟩
    have e2 : Out.jK V ≫ g = g0 := huniq _ ⟨by rw [Category.assoc, hg, hxy], κA ≫ χA, κB ≫ χB,
      hκA.comp hχA, hκB.comp hχB,
      by rw [Category.assoc, hχA1, hκA1], by rw [Category.assoc, hχB1, hκB1],
      by rw [← Category.assoc, hΦV1, Category.assoc, hχΦ, Category.assoc]⟩
    exact ⟨g, e2.trans e1.symm, hg⟩
  haveI : UniversallyClosed R.π := UniversallyClosed.of_valuativeCriterion R.π hex
  exact IsProper.mk

end GlobalTheory.EndLoc.HomFixProper
