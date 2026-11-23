import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open Limits (pullback)
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PPAS

variable {S S' : Scheme.{0}}

theorem one_comp_of_isGrpPullback {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) :
    (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h A'))
  let g : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk φ h.1.w
  have e2 : g ≫ (1 : A ⟶ A) = 1 := by simp
  have e3 := congrArg (fun z : Over.mk (A'.hom ≫ f) ⟶ A => z.left) e2
  simp only [Over.comp_left] at e3
  rw [← e3] at e
  exact e

theorem lift_sqMap {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (a' b' : A' ⟶ A') (a b : A ⟶ A)
    (ha : a'.left ≫ φ = φ ≫ a.left) (hb : b'.left ≫ φ = φ ≫ b.left) :
    (lift a' b').left ≫ sqMap h.1.w = φ ≫ (lift a b).left := by
  apply pullback.hom_ext
  · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    have k₁ : (lift a' b').left ≫ pullback.fst A'.hom A'.hom = a'.left :=
      congrArg (fun z => z.left) (lift_fst a' b')
    have k₂ : (lift a b).left ≫ pullback.fst A.hom A.hom = a.left := congrArg (fun z => z.left) (lift_fst a b)
    rw [← Category.assoc, k₁, k₂, ha]
  · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    have k₁ : (lift a' b').left ≫ pullback.snd A'.hom A'.hom = b'.left :=
      congrArg (fun z => z.left) (lift_snd a' b')
    have k₂ : (lift a b).left ≫ pullback.snd A.hom A.hom = b.left := congrArg (fun z => z.left) (lift_snd a b)
    rw [← Category.assoc, k₁, k₂, hb]

theorem sqToBase_fst {T : Scheme.{0}} (A : Over S) (s : T ⟶ S) :
    IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ pullback.fst A.hom A.hom =
      (fst ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  congrArg (fun z => z.left) (lift_fst (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))

theorem sqToBase_snd {T : Scheme.{0}} (A : Over S) (s : T ⟶ S) :
    IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ pullback.snd A.hom A.hom =
      (snd ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  congrArg (fun z => z.left) (lift_snd (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))

theorem sqToBase_comp_sqMap {A : Over S} {A' : Over S'} {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (w : φ ≫ A.hom = A'.hom ≫ f) {T : Scheme.{0}} (s : T ⟶ S')
    {ψ : ((Over.pullback s).obj A').left ⟶ ((Over.pullback (s ≫ f)).obj A).left}
    (w' : ψ ≫ ((Over.pullback (s ≫ f)).obj A).hom = ((Over.pullback s).obj A').hom ≫ 𝟙 T)
    (hψ : ψ ≫ pullback.fst A.hom (s ≫ f) = pullback.fst A'.hom s ≫ φ) :
    IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A' s ≫ sqMap w = sqMap w' ≫ IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A (s ≫ f) := by
  apply pullback.hom_ext
  · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_fst]
    rw [sqToBase_fst, ← Category.assoc, sqToBase_fst]
    show pullback.fst _ _ ≫ pullback.fst A'.hom s ≫ φ =
      pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst A.hom (s ≫ f)
    rw [pullback.lift_fst_assoc, Category.assoc, hψ]
  · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_snd]
    rw [sqToBase_snd, ← Category.assoc, sqToBase_snd]
    show pullback.snd _ _ ≫ pullback.fst A'.hom s ≫ φ =
      pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ pullback.fst A.hom (s ≫ f)
    rw [pullback.lift_snd_assoc, Category.assoc, hψ]

theorem isPrincipalPol_pull {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {c : CechPic.Pic (A ⊗ A).left}
    (hc : IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) :
    IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A' (CechPic.pull (sqMap h.1.w) c) := by
  have h1 := one_comp_of_isGrpPullback h
  refine ⟨?_, ?_, fun Ω _ _ s => ?_⟩
  · rw [← CechPic.pull_comp, lift_sqMap h _ _ 1 (𝟙 A) h1 (by simp), CechPic.pull_comp, hc.1, map_zero]
  · rw [← CechPic.pull_comp, lift_sqMap h _ _ (𝟙 A) 1 (by simp) h1, CechPic.pull_comp, hc.2.1, map_zero]
  · obtain ⟨L, hL, hA, hK, hcL⟩ := hc.2.2 Ω (s ≫ f)
    have hB' := (isGrpPullback_pullback A' s).comp h
    have hB := isGrpPullback_pullback A (s ≫ f)
    obtain ⟨e, he, hφ⟩ := grpPullback_iso hB' hB
    have h₁ := isGrpPullback_of_iso e
    have hL' := pull_isLB hL e.hom.left
    obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hL' hL').1 rfl
    refine ⟨_, hL', relAmple_pull h₁.1 hL hL' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _)
      (fun _ => trivial) hA, kTriv_pull h₁ hL hL' ((isGen_iff w).1 hw) hK, ?_⟩
    rw [← CechPic.pull_comp, sqToBase_comp_sqMap h.1.w s h₁.1.w hφ, CechPic.pull_comp, hcL,
      pull_sqMap_lam h₁, CechPic.cls_pull hL]

theorem exists_pull (S S' : Scheme.{0}) (P : PPAS S) (f : S' ⟶ S) :
    ∃ (P' : PPAS S') (φ : P'.A.left ⟶ P.A.left), P'.g = P.g ∧ P'.IsPull P f φ := by
  have h := isGrpPullback_pullback P.A f
  exact ⟨{ A := (Over.pullback f).obj P.A
           isAb := PolPull.isAbelianScheme_of_isGrpPullback P.isAb h
           g := P.g
           smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
           c := CechPic.pull (sqMap h.1.w) P.c
           isPol := isPrincipalPol_pull h P.isPol }, pullback.fst P.A.hom f, rfl, h, rfl⟩
end GlobalTheory.PPAS
