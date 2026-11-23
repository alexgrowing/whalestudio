import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialLocusRigidifiedBundleClosedSeesawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndPullOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommMonObjOfGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixTrivLocus

theorem lbIso_pull_comp' {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem isoLocus_closed : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (Z₁ : Scheme.{0}) [IsLocallyNoetherian Z₁] (t₁ : Z₁ ⟶ Sp Rg) (A₁ B₁ : Over Z₁) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → RelAmple A L → IsGrpPullback A₁ A t₁ φA₁ → IsGrpPullback B₁ B t₁ φB₁ → IsMonHom Φ₁ → ∃ (Z : Scheme.{0}) (i : Z ⟶ Z₁), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (u : T ⟶ Z₁) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A₁ u ψA → IsGrpPullback B' B₁ u ψB → Φ'.left ≫ ψB = ψA ≫ Φ₁.left → (LBIso (L.pull (ψA ≫ φA₁)) ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ↔ ∃ w : T ⟶ Z, w ≫ i = u) := by
  intro Rg _ A B _ _ L M eA eB Z₁ _ t₁ A₁ B₁ _ _ φA₁ φB₁ Φ₁ hA hB hL hM hgA hgB hamp hpA hpB hΦ
  haveI : IsMonHom Φ₁ := hΦ
  haveI : IsCommMonObj A := hA.comm
  haveI : IsCommMonObj A₁ := GlobalTheory.isCommMonObj_of_grpPullback _ _ A A₁ t₁ φA₁ hpA
  obtain ⟨hA₁, hL₁, hrA₁, haA₁⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ t₁ A A₁ φA₁ L
    hpA hA hL ⟨eA, hgA⟩ hamp
  have hrB₁ : Out.Rigidified B₁ (M.pull φB₁) := GlobalTheory.PolBaseChange.rigidified_pull hpB ⟨eB, hgB⟩
  have hM₁ : (M.pull (Φ₁.left ≫ φB₁)).IsLB := pull_isLB hM _
  have hN : (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁)).IsLB := LB.isLB_div hM₁ hL₁
  have hrN : Out.Rigidified A₁ (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁)) := by
    refine (GlobalTheory.IsoExtend.lbIso_pull_iff_gen (L.pull φA₁) (M.pull (Φ₁.left ≫ φB₁)) (eSec A₁)).1 ?_
    obtain ⟨s, hs⟩ := hrA₁
    obtain ⟨t, ht⟩ := hrB₁
    have e1 : LBIso ((L.pull φA₁).pull (eSec A₁)) ((M.pull φB₁).pull (eSec B₁)) :=
      GlobalTheory.SabMapDescent.lbIso_of_gen_of_gen s hs t ht
    have hc : eSec A₁ ≫ Φ₁.left = eSec B₁ := congrArg (fun z => z.left) (IsMonHom.one_hom Φ₁)
    have e2 : LBIso ((M.pull φB₁).pull (eSec B₁)) ((M.pull (Φ₁.left ≫ φB₁)).pull (eSec A₁)) :=
      GlobalTheory.HomFixTransport.lbIso_pull_pull hM _ _ _ _ (by rw [← Category.assoc, hc])
    exact LBIso.trans (pull_isLB hL₁ _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM₁ _) e1 e2
  obtain ⟨Z, i, hi, H⟩ := GlobalTheory.T.trivial_locus_rigidified_bundle_closed_seesaw Z₁ A₁ (L.pull φA₁) (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁))
    hA₁ hL₁ haA₁ hN hrN
  refine ⟨Z, i, hi, fun T u A' B' _ _ ψA ψB Φ' hpA' hpB' hc => ?_⟩
  refine Iff.trans ?_ ((GlobalTheory.IsoExtend.lbIso_pull_iff_gen (L.pull φA₁) (M.pull (Φ₁.left ≫ φB₁)) ψA).trans
    (H T u A' ψA hpA'))
  have a1 : LBIso (L.pull (ψA ≫ φA₁)) ((L.pull φA₁).pull ψA) := lbIso_pull_comp' hL φA₁ ψA
  have a2 : LBIso ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ((M.pull (Φ₁.left ≫ φB₁)).pull ψA) :=
    GlobalTheory.HomFixTransport.lbIso_pull_pull hM _ _ _ _ (by rw [← Category.assoc, hc, Category.assoc])
  have h1 := pull_isLB hL (ψA ≫ φA₁)
  have h2 := pull_isLB hL₁ ψA
  have h3 := pull_isLB (pull_isLB hM (ψB ≫ φB₁)) Φ'.left
  have h4 := pull_isLB hM₁ ψA
  exact ⟨fun h => GlobalTheory.HomFixTransport.lbIso_congr h1 h2 h3 h4 (LBIso.symm a1) h a2,
    fun h => GlobalTheory.HomFixTransport.lbIso_congr h2 h1 h4 h3 a1 h (LBIso.symm a2)⟩

end GlobalTheory.HomFixTrivLocus
