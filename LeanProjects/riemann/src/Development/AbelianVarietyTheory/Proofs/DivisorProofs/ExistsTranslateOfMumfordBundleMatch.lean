import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyOfTrivialModEpsilon
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem pull_inv_cls {R : Type} [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) :
    pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
  obtain ⟨U, hU, t, ht⟩ := P.sym (IsLocalRing.closedPoint R)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  have h := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 ⟨t, ht⟩
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul, pull_comp] at h
  obtain ⟨m, hm⟩ : ∃ m : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme, m ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨P.A.left.topIso.inv, P.A.left.topIso.inv_hom_id⟩
  have h' := congrArg (pull m) h
  rw [map_add, map_neg, map_zero, ← pull_comp m, ← pull_comp m, hm, pull_id, pull_id, add_neg_eq_zero] at h'
  exact h'

theorem pull_one_eq_zero {R : Type} [CommRing R] [IsLocalRing R] {G Y : Over (Sp R)} [GrpObj G] (d : Pic G.left) :
    pull (1 : Y ⟶ G).left d = 0 := by
  have e : (1 : Y ⟶ G) = toUnit Y ≫ η[G] := rfl
  rw [e, Over.comp_left, pull_comp, GlobalTheory.DualOpen.pic_sp_local_eq_zero R (pull η[G].left d), map_zero]

theorem exists_translate_of_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D₀ D : DegPre R)
  (β : D₀.P.A ≅ D.P.A), IsMonHom β.hom →
  (∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
      ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
    wΛ.IsGen) →
  ∃ b : 𝟙_ (Over (Sp R)) ⟶ D.P.A, padd D.P.A b b = η[D.P.A] ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β.hom b) GlobalTheory.MumCmp.twε), w.IsGen := by
  intro R _ _ _ _ D₀ D β hβ hw
  have := D.P.isAb.comm
  have := D₀.P.isAb.comm
  have hL₀ := D₀.P.isLB
  have hL := D.P.isLB
  set c₀ := cls D₀.P.L hL₀ with hc₀
  set c := cls D.P.L hL with hc
  have hd : IsDual D.P.A D.P.A (abelian₂ D.P.A D.P.L) :=
    CompanionTheory.PfDual.kTrivDual R D.P.A D.P.g D.P.isAb D.P.smoothDim D.P.L hL D.P.ktriv
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := hd.isLB
  have e : ∀ (Y : Over (Sp R)) (a t : Y ⟶ D.P.A), evc hΛ a t = lam c a t := fun Y a t ↦ by
    rw [evc, show cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) from
      cls_cube_two hL _ _ hΛ, pull_lam, lift_fst, lift_snd]
  have l₁ : ∀ (Y : Over (Sp R)) (a a' t : Y ⟶ D.P.A), lam c (a * a') t = lam c a t + lam c a' t :=
    fun Y a a' t ↦ by
      rw [← e, ← e, ← e]
      exact (isAdditive_iff hΛ).1 hd.additive Y a a' t
  have l₂ : ∀ (Y : Over (Sp R)) (a t t' : Y ⟶ D.P.A), lam c a (t * t') = lam c a t + lam c a t' :=
    fun Y a t t' ↦ by rw [lam_comm, l₁, lam_comm _ t, lam_comm _ t']

  obtain ⟨wΛ, hwΛ⟩ := hw
  have hΛ₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := LB.isLB_linComb hL₀ _ _
  have eΛ : lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) =
      lam c (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) := by
    have h := (cls_eq_iff hΛ₀ (pull_isLB hΛ _)).2 ⟨wΛ, hwΛ⟩
    have h₁ : cls _ hΛ₀ = lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) := cls_cube_two hL₀ _ _ hΛ₀
    have h₂ : cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) := cls_cube_two hL _ _ hΛ
    rw [← h₁, h, cls_pull hΛ, h₂, pull_lam, lift_fst, lift_snd]
  have s₁ : ∀ (Y : Over (Sp R)) (u v : Y ⟶ D₀.P.A), lam c₀ u v = lam c (u ≫ β.hom) (v ≫ β.hom) := fun Y u v ↦ by
    have h := congrArg (pull (lift u v).left) eΛ
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h

  have Fadd : ∀ (Y : Over (Sp R)) (a a' : Y ⟶ D.P.A),
      pull ((a * a') ≫ β.inv).left c₀ - pull (a * a').left c =
        (pull (a ≫ β.inv).left c₀ - pull a.left c) + (pull (a' ≫ β.inv).left c₀ - pull a'.left c) := by
    intro Y a a'
    have h := s₁ Y (a ≫ β.inv) (a' ≫ β.inv)
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, lam, pull_one_eq_zero, add_zero] at h
    rw [MonObj.mul_comp, ← sub_eq_zero]
    have h' := sub_eq_zero.2 h
    convert h' using 1
    abel
  let N : LB (D.P.A ⊗ 𝟙_ (Over (Sp R))).left :=
    tens (D₀.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left)
      (dual (D.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R)))).left))
  have hN : N.IsLB := isLB_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _))
  have clsN : cls N hN = pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left c₀ -
      pull (fst D.P.A (𝟙_ (Over (Sp R)))).left c := by
    rw [show cls N hN = _ from cls_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _)) hN,
      cls_dual (pull_isLB hL _), cls_pull hL₀, cls_pull hL, sub_eq_add_neg]
  have evN : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A) (t : Y ⟶ 𝟙_ (Over (Sp R))),
      evc hN a t = pull (a ≫ β.inv).left c₀ - pull a.left c := by
    intro Y a t
    rw [evc, clsN, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, lift_fst_assoc, lift_fst]
  have hadd : IsAdditive N := (isAdditive_iff hN).2 fun Y a a' t ↦ by rw [evN, evN, evN, Fadd]
  obtain ⟨b, hb, -⟩ := hd.univ _ N hN hadd
  have eb := (cls_eq_iff hN (pull_isLB hΛ _)).2 hb
  have key : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A),
      pull (a ≫ β.inv).left c₀ - pull a.left c = lam c a (toUnit Y ≫ b) := by
    intro Y a
    have h : evc hN a (toUnit Y) = evc hΛ a (toUnit Y ≫ b) := by
      have h := congrArg (pull (lift a (toUnit Y)).left) eb
      rw [cls_pull hΛ] at h
      change evc hN a (toUnit Y) = pull (lift a (toUnit Y)).left
        (evc hΛ (fst D.P.A (𝟙_ (Over (Sp R)))) (snd D.P.A (𝟙_ (Over (Sp R))) ≫ b)) at h
      rw [pull_evc, lift_fst, lift_snd_assoc] at h
      exact h
    rw [← evN Y a (toUnit Y), h, e]
  refine ⟨b, ?_, ?_⟩
  ·
    have sym₀ : pull (GrpObj.inv : D₀.P.A ⟶ D₀.P.A).left c₀ = c₀ := pull_inv_cls D₀.P
    have sym : pull (GrpObj.inv : D.P.A ⟶ D.P.A).left c = c := pull_inv_cls D.P
    have odd : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A), lam c a (toUnit Y ≫ b) + lam c a (toUnit Y ≫ b) = 0 := by
      intro Y a
      have ia : a⁻¹ = a ≫ GrpObj.inv := rfl
      have ia' : (a ≫ β.inv)⁻¹ = (a ≫ β.inv) ≫ GrpObj.inv := rfl
      have h₁ : lam c a⁻¹ (toUnit Y ≫ b) = lam c a (toUnit Y ≫ b) := by
        rw [← key, ← key, GrpObj.inv_comp, ia, ia']
        simp only [Over.comp_left, pull_comp, sym₀, sym]
      have h₂ : lam c (a⁻¹ * a) (toUnit Y ≫ b) = 0 := by rw [inv_mul_cancel, lam_one_left]
      rw [l₁, h₁] at h₂
      exact h₂
    have two : b * b = 1 := by
      refine hd.eq_one (b * b) ((triv_ev_iff hΛ _ _).2 ?_)
      have hs : snd D.P.A (𝟙_ (Over (Sp R))) = toUnit _ := toUnit_unique _ _
      rw [e, hs, MonObj.comp_mul, l₂, odd]
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by
      rw [show (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = toUnit _ ≫ η[D.P.A] from rfl,
        toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    exact two.trans e₁
  ·
    have hC : (LB.LinComb D.P.L (twφ D₀ D β.hom b) twε).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff hL₀ hC).1 ?_
    have h := key D₀.P.A β.hom
    rw [Iso.hom_inv_id, Over.id_left, pull_id, sub_eq_iff_eq_add] at h
    have e₁ : padd D.P.A β.hom (toUnit D₀.P.A ≫ b) = β.hom * (toUnit D₀.P.A ≫ b) := rfl
    have e₂ : toUnit D₀.P.A ≫ η[D.P.A] = 1 := rfl
    rw [cls_linComb hL, Fin.sum_univ_three]
    simp only [twφ, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, one_smul, neg_smul, e₁, e₂]
    rw [← hc, ← hc₀, h, lam]
    abel

end GlobalTheory.MumCmp
