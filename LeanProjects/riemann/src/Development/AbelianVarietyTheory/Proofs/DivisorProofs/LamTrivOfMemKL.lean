import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem lam_triv_of_memKL : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left,
    L.IsLB → ∀ (T : Over S) (x : T ⟶ A), GlobalTheory.MemKL A L x → Triv (ev (abelian₂ A L) (fst A T) (snd A T ≫ x)) := by
  intro S A _ hA L hL T x hx
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over S) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  rw [triv_ev_iff hP]
  obtain ⟨M, hM, hc⟩ := cls_surj (evc hP (fst A T) (snd A T ≫ x))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ T).left),
      Triv (M.pull f) ↔ CechPic.pull f (evc hP (fst A T) (snd A T ≫ x)) = 0 := by
    intro X f
    rw [← hc, ← cls_pull hM f (pull_isLB hM f)]
    exact (cls_eq_zero_iff (pull_isLB hM f)).symm
  refine (cls_eq_zero_iff hM).2 (GlobalTheory.CubeGlue.triv_of_locally_triv hM (snd A T).left (lift 1 (𝟙 T)).left ?_
    (surj_restrict_snd hA T) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key, pull_evc, e, lift_fst, lift_snd_assoc, Category.id_comp, lam_one_left]
  · intro p
    obtain ⟨V, hV, hTV⟩ := hx p
    obtain ⟨W, hW, hw⟩ := exists_pull_eq_zero
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
    refine ⟨V ⊓ W, ⟨hV, hW⟩, ?_⟩
    let U := (snd A T).left ⁻¹ᵁ (V ⊓ W)
    let Y : Over S := Over.mk (U.ι ≫ (A ⊗ T).hom)
    let i : Y ⟶ A ⊗ T := Over.homMk U.ι rfl
    show Triv (M.pull i.left)
    rw [key, pull_evc, e]
    have ht : ∀ z, (i ≫ snd A T).left z ∈ V := fun z ↦ z.2.1
    have h1 := pull_mul_eq hL hTV (i ≫ snd A T) ht (i ≫ fst A T)
    have h2 : CechPic.pull (i ≫ snd A T).left
        (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) = 0 :=
      pull_eq_zero_of_mem W (i ≫ snd A T).left (fun z ↦ z.2.2) hw
    rw [map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      Category.assoc] at h2
    rw [lam, mul_comm (i ≫ fst A T), ← Category.assoc i (snd A T) x, h1, Category.assoc, sub_self, zero_sub,
      neg_add_eq_zero]
    exact (sub_eq_zero.1 h2)

end GlobalTheory.DualCon
