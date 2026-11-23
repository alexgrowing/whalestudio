import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleIsoUniformisedGroupGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupSixTermRelationToZpowForm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.Mum.EFixCube

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_cube_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (J : Ideal R), AdmBase R J →
    ∀ (D : DegData R J) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre J D A G), IsSemiAbelian G → ∀ (x y x' y' : G ⟶ G) (cx cy cx' cy' : A.A ⟶ A.A),
    Gen₀ U U x cx → Gen₀ U U y cy → Gen₀ U U x' cx' → Gen₀ U U y' cy' →
    LBIso (cubeLB A.A ![fst A.A A.A ≫ cx, snd A.A A.A ≫ cy] A.L) (cubeLB A.A ![fst A.A A.A ≫ cx', snd A.A A.A ≫ cy'] A.L) →
    LBIso (cubeLB G ![fst G G ≫ x, snd G G ≫ y] U.LG.L) (cubeLB G ![fst G G ≫ x', snd G G ≫ y'] U.LG.L) := by
  intro R _ _ _ J hR D₁ A₁ G₁ _ _ U₁ hS x₁ y₁ x₂ y₂ cx₁ cy₁ cx₂ cy₂ hx₁ hy₁ hx₂ hy₂ hA
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G₁ G₁
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G₁ G₁
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G₁ G₁
  let u := lift (fst ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
  have key : ∀ (x y : G₁ ⟶ G₁) (cx cy : A₁.A ⟶ A₁.A), Gen₀ U₁ U₁ x cx → Gen₀ U₁ U₁ y cy →
      CechPic.pull (pullback.fst (G₁ ⊗ G₁).hom (jK R)) (cubeCls G₁ ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (cls U₁.LG.L U₁.LG.isLB)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx, snd A₁.A A₁.A ≫ cy] (cls A₁.L A₁.isLB))) := by
    intro x y cx cy hx hy
    have hL := U₁.LG.isLB
    have hA := A₁.isLB
    have hgen := U₁.gen_hom
    have hc' : CechPic.pull (pullback.fst G₁.hom (jK R)) (cls U₁.LG.L hL) =
        CechPic.pull U₁.gen.hom.left (cls A₁.L hA) := by
      obtain ⟨w, hw⟩ := U₁.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    have hu : u.left ≫ (A₁.A ⊗ A₁.A).hom =
        ((Over.pullback (jK R)).obj G₁ ⊗ (Over.pullback (jK R)).obj G₁).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e' := push_cubeCls (isGrpPullback_pullback G₁ (jK R)) (T' := (Over.pullback (jK R)).obj (G₁ ⊗ G₁))
      (T := G₁ ⊗ G₁) (fun i => (Over.pullback (jK R)).map (![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] i))
      ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (pullback.fst (G₁ ⊗ G₁).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U₁.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U₁.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U₁.gen.hom).left = (u ≫ fst A₁.A A₁.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U₁.gen.hom).left = (u ≫ snd A₁.A A₁.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have hL₁ := U₁.LG.isLB
  have hA₁ := A₁.isLB
  have l₁ : (cubeLB G₁ ![fst G₁ G₁ ≫ x₁, snd G₁ G₁ ≫ y₁] U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have l₂ : (cubeLB G₁ ![fst G₁ G₁ ≫ x₂, snd G₁ G₁ ≫ y₂] U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have m₁ : (cubeLB A₁.A ![fst A₁.A A₁.A ≫ cx₁, snd A₁.A A₁.A ≫ cy₁] A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have m₂ : (cubeLB A₁.A ![fst A₁.A A₁.A ≫ cx₂, snd A₁.A A₁.A ≫ cy₂] A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have eA : cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx₁, snd A₁.A A₁.A ≫ cy₁] (cls _ hA₁) =
      cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx₂, snd A₁.A A₁.A ≫ cy₂] (cls _ hA₁) :=
    (cls_cubeLB _ _ hA₁).symm.trans (((cls_eq_iff m₁ m₂).2 hA).trans (cls_cubeLB _ _ hA₁))
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G₁ ⊗ G₁) (η[G₁ ⊗ G₁]).left (Over.w _) _ _ l₁ l₂ ?_
  refine (cls_eq_iff (pull_isLB l₁ _) (pull_isLB l₂ _)).1 ?_
  rw [cls_pull l₁ _ (pull_isLB l₁ _), cls_pull l₂ _ (pull_isLB l₂ _), cls_cubeLB _ _ hL₁, cls_cubeLB _ _ hL₁,
    key x₁ y₁ cx₁ cy₁ hx₁ hy₁, key x₂ y₂ cx₂ cy₂ hx₂ hy₂, eA]

theorem cube_adj_of_oLinear : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G), IsSemiAbelian G → ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X]
    (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.OLinear O ιD ιA ιG → ∀ a : O,
    LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ U hS O _ _ _ ιD ιA ιG hl a
  have g₁ : Gen₀ U U (𝟙 G) (𝟙 A.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hA := GlobalTheory.AdjPolLocal.lbIso_of_rosatiAdj_local (FractionRing R) A.A A.L (ιA.act a) (ιA.act (star a)) A.isLB (ιA.rosati a)
  have := lbIso_cube_of_generic R _ hR D A G U hS (ιG.act a) (𝟙 G) (𝟙 G) (ιG.act (star a)) (ιA.act a) (𝟙 A.A) (𝟙 A.A)
    (ιA.act (star a)) (hl.ext a) g₁ g₁ (hl.ext (star a)) (by simpa only [Category.comp_id] using hA)
  simpa only [Category.comp_id] using this

end GlobalTheory.Mum.EFixCube
