import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistFlat

theorem pull_cls_translDiff_div {S : Scheme.{0}} {A T Y Z : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hL : L.IsLB) (hP : (abelian₂ A L).IsLB) {N : LB (A ⊗ T).left} (hN : N.IsLB) (a : Y ⟶ A) (t : Y ⟶ T)
    (hD : (LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).IsLB) (s : Z ⟶ Y) (u : Z ⟶ A) :
    CechPic.pull (lift s u).left (cls _ hD) = evc hP u (s ≫ a) - evc hN u (s ≫ t) +
      CechPic.pull s.left (CechPic.pull a.left (cls L hL) - CechPic.pull (1 : Y ⟶ A).left (cls L hL)) := by
  have hT : (translDiff A L a).IsLB := LB.isLB_linComb hL _ _
  rw [cls_div hT (pull_isLB hN _) hD, map_sub, GlobalTheory.AbDual.pull_translDiff hL a hT, cls_ev hN, pull_evc, lift_snd,
    lift_fst_assoc, GlobalTheory.CubeDual.evc_lam hL, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left,
    MonObj.comp_one, lam, _root_.mul_comm u (s ≫ a)]
  abel

theorem same_lam_iff_locally_triv : ∀ {S : Scheme.{0}} (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), Fam A N → ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∀ p : Y.left, ∃ U : Y.left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).pull ((fst Y A).left ⁻¹ᵁ U).ι) := by
  intro S A T _ hA L hL N hN Y a t
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hF : Fam A (abelian₂ A L) := ⟨hP, (GlobalTheory.CubeDual.isAdditive_lam GlobalTheory.CubeTop.cubeTheorem hA hL hP).1⟩
  have hT : (translDiff A L a).IsLB := LB.isLB_linComb hL _ _
  have hD : (LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).IsLB :=
    LB.isLB_div hT (pull_isLB hN.isLB _)
  constructor
  · intro h p
    obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
      (CechPic.pull a.left (cls L hL) - CechPic.pull (1 : Y ⟶ A).left (cls L hL)) p
    refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
    have e₁ := pull_cls_translDiff_div hL hP hN.isLB a t hD (fst Y A) (snd Y A)
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have e₂ := congrArg (CechPic.pull (lift (snd Y A) (fst Y A)).left) ((same_iff hP hN.isLB a t).1 h)
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc] at e₂
    rw [cls_pull hD, e₁, e₂, sub_self, zero_add, ← pull_comp]
    exact pull_eq_zero_of_mem V (((fst Y A).left ⁻¹ᵁ V).ι ≫ (fst Y A).left) (fun z ↦ z.2) hc
  · intro h
    refine same_of_local S A A T hA _ N hF hN Y a t fun p ↦ ?_
    obtain ⟨U, hU, hU'⟩ := h p
    obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
      (CechPic.pull a.left (cls L hL) - CechPic.pull (1 : Y ⟶ A).left (cls L hL)) p
    let Z : Over S := Over.mk ((U ⊓ V).ι ≫ Y.hom)
    let z : Z ⟶ Y := Over.homMk (U ⊓ V).ι rfl
    refine ⟨Z, z, inferInstanceAs (IsOpenImmersion (U ⊓ V).ι), ⟨⟨p, hU, hV⟩, rfl⟩, ?_⟩
    rw [same_iff hP hN.isLB, ← sub_eq_zero]
    have hm : ∀ w, (snd A Z ≫ z).left w ∈ U ⊓ V := fun w ↦ ((snd A Z).left w).2
    have e₁ := pull_cls_translDiff_div hL hP hN.isLB a t hD (snd A Z ≫ z) (fst A Z)
    have z₀ : CechPic.pull ((fst Y A).left ⁻¹ᵁ U).ι (cls _ hD) = 0 := (cls_eq_zero_iff (pull_isLB hD _)).2 hU'
    have e : (lift (snd A Z ≫ z) (fst A Z)).left ≫ (fst Y A).left = (snd A Z ≫ z).left := by
      rw [← Over.comp_left, lift_fst]
    rw [pull_eq_zero_of_mem _ _ (fun w ↦ (congrArg (fun q ↦ q w ∈ U) e).mpr (hm w).1) z₀,
      pull_eq_zero_of_mem V _ (fun w ↦ (hm w).2) hc, add_zero, Category.assoc, Category.assoc] at e₁
    exact e₁.symm

end GlobalTheory.TwistFlat
