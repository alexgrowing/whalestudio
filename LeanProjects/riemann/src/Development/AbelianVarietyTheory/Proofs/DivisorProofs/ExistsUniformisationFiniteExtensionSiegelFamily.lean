import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtSameMumfordBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtLam
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegDataFiniteUnramified
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.IsLocalHomAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.PoincUnif

theorem exists_unif_finExt : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁]
    [IsLocalRing V₁], GlobalTheory.LN.CDvr V₁ → ∀ (y₁ : Sp (FractionRing V₁) ⟶ F.X) (A : PolAV (Sp (FractionRing V₁)))
    (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
    IsGrpPullback A.A F.univ.A y₁ α → IsSquare α α₂ → LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) →
    ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G] (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
    IsSemiAbelian G → IsMonHom gen.hom →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V₁ →+* W)
        (fK : FractionRing V₁ →+* FractionRing W), GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V₁ _ a) = algebraMap W _ (f a)) ∧
        ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (D : DegData W (maximalIdeal W))
          (A' : PolAV (Sp (FractionRing W))) (_ : Unif (maximalIdeal W) D A' G') (α' : A'.A.left ⟶ F.univ.A.left)
          (α₂' : (G2 A'.A).left ⟶ (G2 F.univ.A).left),
          IsSemiAbelian G' ∧ IsGrpPullback A'.A F.univ.A (spMap fK ≫ y₁) α' ∧ IsSquare α' α₂' ∧
          LBIso (abelian₂ A'.A A'.L) (F.univ.P.pull α₂') := by
  intro g n o _ ζ F V₁ _ _ _ hV y₁ A α α₂ hα hsq hL G _ _ gen hG hgen
  haveI : IsMonHom gen.hom := hgen
  have hdvr : IsDiscreteValuationRing V₁ := hV.1
  have hLgen : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  obtain ⟨PP, hPP⟩ := GlobalTheory.MumExt.exists_extLam V₁ G hG _ hLgen
  obtain ⟨R', _, _, _, ρ, D₁, G₁, _, _, β, β₂, A₁, U₁, hR', hρ, hβ, hβ₂, hPβ⟩ :=
    GlobalTheory.T.exists_uniformisation_finiteExt_sameMumfordBundle V₁ hV G hG A gen hgen PP hPP
  obtain ⟨-, hinj, hfin⟩ := hρ
  have hloc : IsLocalHom ρ := by
    letI := ρ.toAlgebra
    haveI : Module.Finite V₁ R' := hfin
    exact ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.isLocalHom_algebraMap
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hinj
  let fK : FractionRing V₁ →+* FractionRing R' := IsFractionRing.lift (K := FractionRing V₁) hinj'
  have hfK : ∀ a, fK (algebraMap V₁ _ a) = algebraMap R' _ (ρ a) := fun a =>
    IsFractionRing.lift_algebraMap _ _
  have hbase : jK R' ≫ spMap ρ = spMap fK ≫ jK V₁ := by
    have e : fK.comp (algebraMap V₁ (FractionRing V₁)) = (algebraMap R' (FractionRing R')).comp ρ :=
      RingHom.ext hfK
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom e.symm

  let g₁ : A₁.A.left ⟶ G₁.left := U₁.gen.inv.left ≫ pullback.fst G₁.hom (jK R')
  have hg₁ : IsGrpPullback A₁.A G₁ (jK R') g₁ := GlobalTheory.ThetaBaseChange.grp_generic U₁.toUnifPre
  have hgβ := hg₁.comp hβ
  have hfst : IsGrpPullback ((Over.pullback (jK V₁)).obj G) G (jK V₁) (pullback.fst G.hom (jK V₁)) :=
    isGrpPullback_pullback G (jK V₁)
  have hw : (g₁ ≫ β) ≫ G.hom = (A₁.A.hom ≫ spMap fK) ≫ jK V₁ := by
    have := hgβ.1.w
    simp only [Category.assoc] at this ⊢
    rw [← hbase]; exact this
  let ι' : A₁.A.left ⟶ ((Over.pullback (jK V₁)).obj G).left := hfst.1.lift (g₁ ≫ β) (A₁.A.hom ≫ spMap fK) hw
  have hι'f : ι' ≫ pullback.fst G.hom (jK V₁) = g₁ ≫ β := hfst.1.lift_fst _ _ _
  have hι's : ι' ≫ ((Over.pullback (jK V₁)).obj G).hom = A₁.A.hom ≫ spMap fK := hfst.1.lift_snd _ _ _
  have hι' : IsGrpPullback A₁.A ((Over.pullback (jK V₁)).obj G) (spMap fK) ι' :=
    IsGrpPullback.cancel hfst (hgβ.congr hbase hι'f.symm) hι's
  let ι : A₁.A.left ⟶ A.A.left := ι' ≫ gen.hom.left
  have hι : IsGrpPullback A₁.A A.A (spMap fK) ι :=
    (hι'.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  have hα' : IsGrpPullback A₁.A F.univ.A (spMap fK ≫ y₁) (ι ≫ α) := hι.comp hα

  obtain ⟨ι₂, hι₂⟩ : ∃ m, IsSquare ι m := ⟨_, GlobalTheory.LamPull.exists_isSquare hι.1.w⟩
  obtain ⟨ι'₂, hι'₂⟩ : ∃ m, IsSquare ι' m := ⟨_, GlobalTheory.LamPull.exists_isSquare hι'.1.w⟩
  obtain ⟨g₁₂, hg₁₂⟩ : ∃ m, IsSquare g₁ m := ⟨_, GlobalTheory.LamPull.exists_isSquare hg₁.1.w⟩
  obtain ⟨κ₂, hκ₂⟩ : ∃ m, IsSquare (G' := (Over.pullback (jK V₁)).obj G) (G := G) (pullback.fst G.hom (jK V₁)) m :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hfst.1.w⟩
  have sqc : ∀ {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
      {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left},
      IsSquare ψ ψ₂ → IsSquare φ φ₂ → IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := fun h' h =>
    ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
      by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩
  have hsq' := sqc hι₂ hsq
  have e₂ := GlobalTheory.LamPull.isSquare_unique (sqc hg₁₂ hβ₂) (hι'f ▸ sqc hι'₂ hκ₂)

  have hPPlb : PP.IsLB := hPP.1
  have hA₁L : LBIso A₁.L (U₁.LG.L.pull g₁) := by
    have hgi : U₁.gen.inv.left ≫ U₁.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    exact LBIso.chartPull (h := U₁.gen.inv.left) (chartPullSec A₁.L _ _ hgi)
      (chartPullSame U₁.LG.L _ (fun _ => pullback.fst G₁.hom (jK R')) _ _ fun _ => rfl) U₁.ext
  have lamLB : ∀ {S : Scheme.{0}} (X : Over S) [GrpObj X] [IsCommMonObj X] {M : LB X.left}, M.IsLB →
      (abelian₂ X M).IsLB := fun X _ _ M hM => DVR.linComb_isLB M hM _ _
  have s1 := GlobalTheory.LamPull.lbIso_lam_pull hg₁ U₁.LG.isLB A₁.isLB hA₁L hg₁₂
  have s2 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull hPβ g₁₂
  rw [e₂] at s2
  have s3 := (GlobalTheory.ZM.SiegClause.lbIso_pull_pull (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hPPlb κ₂)) ι'₂).symm
  have s4 := hPP.2 κ₂ hκ₂
  have s5 := (GlobalTheory.RigidBundleGlue.LBIso.pull s4 ι'₂).symm
  have hιL : LBIso (A.L.pull ι) ((A.L.pull gen.hom.left).pull ι') :=
    (GlobalTheory.ZM.SiegClause.lbIso_pull_pull (GlobalTheory.PolBaseChange.lbIso_refl hLgen) ι').symm
  have s6 := (GlobalTheory.LamPull.lbIso_lam_pull hι' hLgen (pull_isLB A.isLB ι) hιL hι'₂).symm
  have s7 := GlobalTheory.LamPull.lbIso_lam_pull hι A.isLB (pull_isLB A.isLB ι)
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A.isLB ι)) hι₂
  have s8 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull hL ι₂
  have t1 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ U₁.LG.isLB) _) (pull_isLB hPPlb _) s1 s2
  have t2 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB hPPlb _) (pull_isLB (pull_isLB hPPlb _) _) t1 s3
  have t3 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (pull_isLB hPPlb _) _) (pull_isLB (lamLB _ hLgen) _) t2 s5
  have t4 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ hLgen) _) (lamLB _ (pull_isLB A.isLB ι)) t3 s6
  have t5 := LBIso.trans (lamLB _ A₁.isLB) (lamLB _ (pull_isLB A.isLB ι)) (pull_isLB (lamLB _ A.isLB) _) t4 s7
  have t6 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ A.isLB) _) (pull_isLB F.univ.isLB _) t5 s8
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap ρ))
    haveI := mbc
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap ρ) G hG)
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ, fK, hR', hinj, hloc, hfin, hfK, G₁, inferInstance,
    inferInstance, D₁, A₁, U₁, ι ≫ α, _, hG₁, hα', hsq', t6⟩

end GlobalTheory.PoincUnif
