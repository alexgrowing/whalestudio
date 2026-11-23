import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationDataNormalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc

open GlobalTheory.CechPic in

theorem lam_trait_fibre_eq_univ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (fK : FractionRing T.V →+* FractionRing W) (G'' : Over (Sp W)) [GrpObj G''] (β : G''.left ⟶ T.G.left) (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left), IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ → κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β → ∀ (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left), IsSquare (κ ≫ T.α) α₂ → LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β))) (F.univ.P.pull α₂) := by
  intro g n o _ ζ F T W _ _ fK G'' _ β κ hκ hκβ α₂ hα₂
  have hL := T.U.LG.isLB
  have hA := T.A.isLB
  have hP := F.univ.isLB
  have hLβ := pull_isLB hL (pullback.fst G''.hom (jK W) ≫ β)
  have hB₁ : (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β))).IsLB :=
    LB.isLB_linComb hLβ _ _
  refine (cls_eq_iff hB₁ (pull_isLB hP α₂)).1 ?_
  have c₂ : cls _ hB₁ = lam (CechPic.pull (pullback.fst G''.hom (jK W) ≫ β) (cls _ hL))
      (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))
      (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')) := by
    rw [← cls_pull hL _ hLβ]; exact cls_cube_two hLβ _ _ hB₁
  have hext : CechPic.pull T.U.gen.hom.left (cls _ hA) =
      CechPic.pull (pullback.fst T.G.hom (jK T.V)) (cls _ hL) := by
    have := (cls_eq_iff (pull_isLB hA T.U.gen.hom.left) (pull_isLB hL (pullback.fst T.G.hom (jK T.V)))).2 T.U.ext
    rwa [cls_pull hA, cls_pull hL] at this
  have hΛ : lam (cls _ hA) (fst T.A.A T.A.A) (snd T.A.A T.A.A) = CechPic.pull T.α₂ (cls _ hP) := by
    have hl : (abelian₂ T.A.A T.A.L).IsLB := LB.isLB_linComb hA _ _
    have := (cls_eq_iff hl (pull_isLB hP T.α₂)).2 T.lb
    rw [cls_pull hP] at this
    exact (cls_cube_two hA _ _ hl).symm.trans this
  have hgi : T.U.gen.inv.left ≫ T.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have e₁ : CechPic.pull (pullback.fst G''.hom (jK W) ≫ β) (cls _ hL) = CechPic.pull κ (cls _ hA) := by
    rw [← hκβ, pull_comp, pull_comp, ← hext, ← pull_comp T.U.gen.inv.left, hgi, pull_id]
  rw [c₂, e₁, lam_pull_of_isGrpPullback hκ, cls_pull hP]
  set Q := lift (pushHom hκ _ (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')))
    (pushHom hκ _ (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))) with hQdef
  have e₃ : lam (cls _ hA) (pushHom hκ _ (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')))
      (pushHom hκ _ (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))) =
      CechPic.pull Q.left (lam (cls _ hA) (fst T.A.A T.A.A) (snd T.A.A T.A.A)) := by
    rw [pull_lam, lift_fst, lift_snd]
  have hQ : Q.left ≫ T.α₂ = α₂ := by
    refine GlobalTheory.UnifLamFibre.isSquare_unique (φ := κ ≫ T.α) ⟨?_, ?_⟩ hα₂
    · rw [Category.assoc, T.sq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      show ((fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')).left ≫ κ) ≫ T.α = _
      rw [Category.assoc]
    · rw [Category.assoc, T.sq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
      show ((snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')).left ≫ κ) ≫ T.α = _
      rw [Category.assoc]
  rw [e₃, hΛ, ← pull_comp, hQ]

end GlobalTheory.Poinc
