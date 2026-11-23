import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleIsoUniformisedGroupGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_lam_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂), IsSemiAbelian G₁ → ∀ (a : G₁ ⟶ G₂) (cA : A₁.A ⟶ A₂.A), IsMonHom a → IsMonHom cA → Gen₀ U₁ U₂ a cA → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA) (snd A₁.A A₁.A ≫ cA) : G2 A₁.A ⟶ G2 A₂.A).left) → LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ a) (snd G₁ G₁ ≫ a) : G2 G₁ ⟶ G2 G₂).left) := by
  intro R _ _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ hS a cA ha hcA hgen hA
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G₁ G₁
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G₁ G₁
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G₁ G₁
  let u := lift (fst ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
  have key : ∀ {D : DegData R J} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
      (U : UnifPre J D A G) (x y : G₁ ⟶ G) (cx cy : A₁.A ⟶ A.A), Gen₀ U₁ U x cx → Gen₀ U₁ U y cy →
      CechPic.pull (pullback.fst (G₁ ⊗ G₁).hom (jK R)) (cubeCls G ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (cls U.LG.L U.LG.isLB)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A₁.A A₁.A ≫ cx, snd A₁.A A₁.A ≫ cy] (cls A.L A.isLB))) := by
    intro D A G _ _ U x y cx cy hx hy
    have hL := U.LG.isLB
    have hA := A.isLB
    have hgen := U.gen_hom
    have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    have hu : u.left ≫ (A₁.A ⊗ A₁.A).hom =
        ((Over.pullback (jK R)).obj G₁ ⊗ (Over.pullback (jK R)).obj G₁).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G₁ ⊗ G₁))
      (T := G₁ ⊗ G₁) (fun i => (Over.pullback (jK R)).map (![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] i))
      ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (pullback.fst (G₁ ⊗ G₁).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U.gen.hom).left = (u ≫ fst A₁.A A₁.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U.gen.hom).left = (u ≫ snd A₁.A A₁.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hA₁ := A₁.isLB
  have hA₂ := A₂.isLB
  have lG₁ : (abelian₂ G₁ U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have lG₂ : (abelian₂ G₂ U₂.LG.L).IsLB := LB.isLB_linComb hL₂ _ _
  have lA₁ : (abelian₂ A₁.A A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have lA₂ : (abelian₂ A₂.A A₂.L).IsLB := LB.isLB_linComb hA₂ _ _
  have g₁ : Gen₀ U₁ U₁ (𝟙 G₁) (𝟙 A₁.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have cG₁ : cls (abelian₂ G₁ U₁.LG.L) lG₁ = cubeCls G₁ ![fst G₁ G₁ ≫ 𝟙 G₁, snd G₁ G₁ ≫ 𝟙 G₁] (cls _ hL₁) := by
    refine (cls_cubeLB G₁ (x2 G₁) hL₁).trans ?_
    congr 1
  have cA₁ : cls (abelian₂ A₁.A A₁.L) lA₁ = cubeCls A₁.A ![fst A₁.A A₁.A ≫ 𝟙 A₁.A, snd A₁.A A₁.A ≫ 𝟙 A₁.A] (cls _ hA₁) := by
    refine (cls_cubeLB A₁.A (x2 A₁.A) hA₁).trans ?_
    congr 1
  have cG₂ : cls ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ a) (snd G₁ G₁ ≫ a) : G2 G₁ ⟶ G2 G₂).left) (pull_isLB lG₂ _) =
      cubeCls G₂ ![fst G₁ G₁ ≫ a, snd G₁ G₁ ≫ a] (cls _ hL₂) := by
    rw [cls_pull lG₂ _ (pull_isLB lG₂ _)]
    refine (congrArg _ (cls_cubeLB G₂ (x2 G₂) hL₂)).trans ?_
    exact pull_cubeCls G₂ _ _ _ (fun i => by fin_cases i <;> simp [x2]) _
  have cA₂ : cls ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA) (snd A₁.A A₁.A ≫ cA) : G2 A₁.A ⟶ G2 A₂.A).left)
      (pull_isLB lA₂ _) = cubeCls A₂.A ![fst A₁.A A₁.A ≫ cA, snd A₁.A A₁.A ≫ cA] (cls _ hA₂) := by
    rw [cls_pull lA₂ _ (pull_isLB lA₂ _)]
    refine (congrArg _ (cls_cubeLB A₂.A (x2 A₂.A) hA₂)).trans ?_
    exact pull_cubeCls A₂.A _ _ _ (fun i => by fin_cases i <;> simp [x2]) _
  have eA : cubeCls A₁.A ![fst A₁.A A₁.A ≫ 𝟙 A₁.A, snd A₁.A A₁.A ≫ 𝟙 A₁.A] (cls _ hA₁) =
      cubeCls A₂.A ![fst A₁.A A₁.A ≫ cA, snd A₁.A A₁.A ≫ cA] (cls _ hA₂) :=
    cA₁.symm.trans (((cls_eq_iff lA₁ (pull_isLB lA₂ _)).2 hA).trans cA₂)
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G₁ ⊗ G₁) (η[G₁ ⊗ G₁]).left (Over.w _) _ _ lG₁ (pull_isLB lG₂ _) ?_
  refine (cls_eq_iff (pull_isLB lG₁ _) (pull_isLB (pull_isLB lG₂ _) _)).1 ?_
  rw [cls_pull lG₁ _ (pull_isLB lG₁ _), cls_pull (pull_isLB lG₂ _) _ (pull_isLB (pull_isLB lG₂ _) _), cG₁, cG₂,
    key U₁ (𝟙 G₁) (𝟙 G₁) (𝟙 A₁.A) (𝟙 A₁.A) g₁ g₁, key U₂ a a cA cA hgen hgen, eA]

end GlobalTheory.TInj
