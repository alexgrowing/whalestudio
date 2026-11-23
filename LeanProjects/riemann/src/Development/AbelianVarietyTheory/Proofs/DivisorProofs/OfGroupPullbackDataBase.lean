import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRepresentableOfCover

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem lbIso_pull {P Q Xa Xb Xa' Xb' : Scheme.{0}} {L : LB P} {M : LB Q} (hL : L.IsLB) (hM : M.IsLB)
    {a : Xa ⟶ P} {b : Xb ⟶ Q} {c : Xa ⟶ Xb} {a' : Xa' ⟶ P} {b' : Xb' ⟶ Q} {c' : Xa' ⟶ Xb'} (e : Xa' ⟶ Xa)
    (ha : a' = e ≫ a) (hc : c' ≫ b' = e ≫ c ≫ b) (H : LBIso (L.pull a) ((M.pull b).pull c)) :
    LBIso (L.pull a') ((M.pull b').pull c') := by
  have h1 : LBIso ((M.pull b).pull c) (M.pull (c ≫ b)) :=
    LBIso.chartPull (chartPullLinComb M b (fun _ : PUnit => c) (fun _ => c ≫ b) (fun _ => 1) (𝟙 _)
      fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hM _))
  have h2 : LBIso (L.pull a) (M.pull (c ≫ b)) :=
    LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) H h1
  exact LBIso.chartPull (chartPullSame L (fun _ : PUnit => a') (fun _ => a) (fun _ => 1) e fun _ => ha)
    (chartPullLinComb M b' (fun _ : PUnit => c') (fun _ => c ≫ b) (fun _ => 1) e fun _ => hc) h2

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)

def Wit {Z : Scheme.{0}} (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left) : Prop :=
  ∃ (A' B' : Over Z) (_ : GrpObj A') (_ : GrpObj B') (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (Φ : A' ⟶ B'),
    IsGrpPullback A' A t φA ∧ IsGrpPullback B' B t φB ∧ IsMonHom Φ ∧ LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∃ e : A'.left ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = φA ∧ e ≫ pullback.snd _ _ = A'.hom ∧ e ≫ f = Φ.left ≫ φB

abbrev pmap {Z Z' : Scheme.{0}} (t : Z ⟶ S) (g : Z' ⟶ Z) : pullback A.hom (g ≫ t) ⟶ pullback A.hom t :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g) (by rw [pullback.condition, Category.assoc])

variable {A B L M}

theorem wit_pull (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left}
    (h : Wit A B L M t f) (g : Z' ⟶ Z) : Wit A B L M (g ≫ t) (pmap A t g ≫ f) := by
  obtain ⟨A', B', _, _, φA, φB, Φ, hA, hB, hΦ, hI, e, e1, e2, e3⟩ := h
  refine ⟨(Over.pullback g).obj A', (Over.pullback g).obj B', inferInstance, inferInstance,
    pullback.fst _ _ ≫ φA, pullback.fst _ _ ≫ φB, (Over.pullback g).map Φ,
    (isGrpPullback_pullback A' g).comp hA, (isGrpPullback_pullback B' g).comp hB, inferInstance, ?_, ?_⟩
  · refine lbIso_pull hL hM (pullback.fst _ _) rfl ?_ hI
    rw [← Category.assoc, show ((Over.pullback g).map Φ).left ≫ pullback.fst B'.hom g =
      pullback.fst A'.hom g ≫ Φ.left from pullback.lift_fst _ _ _, Category.assoc]
  · have hw : (pullback.fst A'.hom g ≫ φA) ≫ A.hom = pullback.snd A'.hom g ≫ g ≫ t := by
      rw [Category.assoc, hA.1.w, ← Category.assoc, pullback.condition, Category.assoc]
    have key : pullback.lift (pullback.fst A'.hom g ≫ φA) (pullback.snd A'.hom g) hw ≫ pmap A t g =
        pullback.fst A'.hom g ≫ e := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, e1]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, e2, pullback.condition]
    refine ⟨pullback.lift (pullback.fst _ _ ≫ φA) (pullback.snd _ _) hw, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _, ?_⟩
    rw [← Category.assoc, key, Category.assoc, e3, ← Category.assoc, ← Category.assoc,
      show ((Over.pullback g).map Φ).left ≫ pullback.fst B'.hom g =
        pullback.fst A'.hom g ≫ Φ.left from pullback.lift_fst _ _ _]

variable (A B L M) in

structure Pt (Z : Scheme.{0}) where

  t : Z ⟶ S

  f : pullback A.hom t ⟶ B.left
  wit : Wit A B L M t f

theorem Pt.ext' {Z : Scheme.{0}} {x y : Pt A B L M Z} (e : x.t = y.t)
    (h : pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition, e]) ≫ x.f = y.f) :
    x = y := by
  obtain ⟨t, f, w⟩ := x
  obtain ⟨t', f', w'⟩ := y
  dsimp only at e h
  revert h
  subst e
  intro h
  rw [pullback.lift_fst_snd, Category.id_comp] at h
  cases h
  rfl

theorem lift_pmap_id {Z : Scheme.{0}} (t : Z ⟶ S) (h : pullback.fst A.hom t ≫ A.hom = pullback.snd A.hom t ≫ 𝟙 Z ≫ t) :
    pullback.lift (pullback.fst A.hom t) (pullback.snd A.hom t) h ≫ pmap A t (𝟙 Z) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]

theorem lift_pmap_comp {Z Z' Z'' : Scheme.{0}} (t : Z ⟶ S) (g : Z' ⟶ Z) (g' : Z'' ⟶ Z')
    (h : pullback.fst A.hom (g' ≫ g ≫ t) ≫ A.hom = pullback.snd A.hom (g' ≫ g ≫ t) ≫ (g' ≫ g) ≫ t) :
    pullback.lift (pullback.fst A.hom (g' ≫ g ≫ t)) (pullback.snd A.hom (g' ≫ g ≫ t)) h ≫ pmap A t (g' ≫ g) =
      pmap A (g ≫ t) g' ≫ pmap A t g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.assoc]

def Pt.map (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} (g : Z' ⟶ Z) (x : Pt A B L M Z) : Pt A B L M Z' :=
  ⟨g ≫ x.t, pmap A x.t g ≫ x.f, wit_pull hL hM x.wit g⟩

theorem Pt.map_id (hL : L.IsLB) (hM : M.IsLB) {Z : Scheme.{0}} (x : Pt A B L M Z) : x.map hL hM (𝟙 Z) = x := by
  refine Pt.ext' (Category.id_comp _) ?_
  show _ ≫ pmap A x.t (𝟙 Z) ≫ x.f = x.f
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x.f) (lift_pmap_id x.t _)).trans (Category.id_comp _))

theorem Pt.map_comp (hL : L.IsLB) (hM : M.IsLB) {Z Z' Z'' : Scheme.{0}} (g : Z' ⟶ Z) (g' : Z'' ⟶ Z')
    (x : Pt A B L M Z) : x.map hL hM (g' ≫ g) = (x.map hL hM g).map hL hM g' := by
  refine Pt.ext' (Category.assoc _ _ _) ?_
  show _ ≫ pmap A x.t (g' ≫ g) ≫ x.f = pmap A (g ≫ x.t) g' ≫ pmap A x.t g ≫ x.f
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x.f) (lift_pmap_comp x.t g g' _)).trans
    (Category.assoc _ _ _))

variable (A B L M) in

def homFun (hL : L.IsLB) (hM : M.IsLB) : Scheme.{0}ᵒᵖ ⥤ Type where
  obj Z := Pt A B L M Z.unop
  map g := TypeCat.ofHom (Pt.map hL hM g.unop)
  map_id Z := by
    ext x
    exact Pt.map_id hL hM x
  map_comp g g' := by
    ext x
    exact Pt.map_comp hL hM _ _ x

variable (A B L M) in

def homProj (hL : L.IsLB) (hM : M.IsLB) : homFun A B L M hL hM ⟶ yoneda.obj S where
  app Z := TypeCat.ofHom fun x => x.t

@[simp] theorem Pt.map_t (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} (g : Z' ⟶ Z) (x : Pt A B L M Z) :
    (x.map hL hM g).t = g ≫ x.t := rfl

def Pt.ofData {Z : Scheme.{0}} (t : Z ⟶ S) (A' B' : Over Z) [GrpObj A'] [GrpObj B'] (φA : A'.left ⟶ A.left)
    (φB : B'.left ⟶ B.left) (Φ : A' ⟶ B') (hA : IsGrpPullback A' A t φA) (hB : IsGrpPullback B' B t φB)
    (hΦ : IsMonHom Φ) (hI : LBIso (L.pull φA) ((M.pull φB).pull Φ.left)) : Pt A B L M Z :=
  ⟨t, hA.1.isoPullback.inv ≫ Φ.left ≫ φB, A', B', inferInstance, inferInstance, φA, φB, Φ, hA, hB, hΦ, hI,
    hA.1.isoPullback.hom, by simp, by simp, by simp⟩

@[simp] theorem Pt.ofGroupPullbackData_base {Z : Scheme.{0}} (t : Z ⟶ S) (A' B' : Over Z) [GrpObj A'] [GrpObj B']
    (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (Φ : A' ⟶ B') (hA : IsGrpPullback A' A t φA)
    (hB : IsGrpPullback B' B t φB) (hΦ : IsMonHom Φ) (hI : LBIso (L.pull φA) ((M.pull φB).pull Φ.left)) :
    (Pt.ofData (L := L) (M := M) t A' B' φA φB Φ hA hB hΦ hI).t = t := rfl

theorem homFun_map (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} (g : Z' ⟶ Z) (x : Pt A B L M Z) :
    (homFun A B L M hL hM).map g.op x = x.map hL hM g := rfl

theorem homProj_app (hL : L.IsLB) (hM : M.IsLB) {Z : Scheme.{0}} (x : Pt A B L M Z) :
    (homProj A B L M hL hM).app (Opposite.op Z) x = x.t := rfl

end GlobalTheory.EndLoc.HomGlue
