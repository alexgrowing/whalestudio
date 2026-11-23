import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} (A : Over S)

def Same {T U Y : Over S} (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) : Prop :=
  LBIso (ev N (fst A Y) (snd A Y ≫ y)) (ev M (fst A Y) (snd A Y ≫ u))

def Inj {U : Over S} (M : LB (A ⊗ U).left) : Prop :=
  ∀ (Y : Over S) (u u' : Y ⟶ U), Same A M M u u' → u = u'

def FibInj {U : Over S} (M : LB (A ⊗ U).left) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (Y : Over S) (_ : Y ⟶ Over.mk s) (u u' : Y ⟶ U),
    Same A M M u u' → u = u'

def ChartAt {U T : Over S} (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) : Prop :=
  ∃ W : T.left.Opens, ∀ (Y : Over S) (y : Y ⟶ T), (∃ u : Y ⟶ U, Same A N M y u) ↔ ∀ z, y.left z ∈ W

structure Good (g : ℕ) {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop where
  proper : IsProper f
  smooth : SmoothOfRelativeDimension g f
  conn : GeometricallyConnected f

def FinAff (X : Scheme.{0}) : Prop :=
  ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U

def DimLe (B : Over S) : Prop :=
  ∀ (g : ℕ) (T : Scheme.{0}) (t : T ⟶ S),
    SmoothOfRelativeDimension g (pullback.snd A.hom t) → SmoothOfRelativeDimension g (pullback.snd B.hom t)

variable [GrpObj A]

structure Fam {T : Over S} (N : LB (A ⊗ T).left) : Prop where
  isLB : N.IsLB
  add : IsAdditive N

structure IsChart {U : Over S} (M : LB (A ⊗ U).left) : Prop where
  fam : Fam A M
  inj : Inj A M
  chart : ∀ (T : Over S) (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N

structure Rep {B S' : Over S} (b : B ⟶ S') (P : LB (A ⊗ B).left) : Prop where
  fam : Fam A P
  univ : ∀ (T : Over S) (t : T ⟶ S') (N : LB (A ⊗ T).left), Fam A N →
    ∃! x : T ⟶ B, x ≫ b = t ∧ LBIso N (ev P (fst A T) (snd A T ≫ x))

def HasRep (g : ℕ) (S' : Over S) : Prop :=
  ∃ (B : Over S) (b : B ⟶ S') (P : LB (A ⊗ B).left), Rep A b P ∧ Good g b.left

def HasRepAF (g : ℕ) (S' : Over S) : Prop :=
  ∃ (B : Over S) (b : B ⟶ S') (P : LB (A ⊗ B).left), Rep A b P ∧ Good g b.left ∧ FinAff B.left

def LiftAt (g : ℕ) {B S' : Over S} (b : B ⟶ S') (P : LB (A ⊗ B).left) (x : B.left) : Prop :=
  ∃ (U : Over S) (M : LB (A ⊗ U).left) (j : U ⊗ S' ⟶ B), Fam A M ∧ SmoothOfRelativeDimension g U.hom ∧
    j ≫ b = snd U S' ∧ IsOpenImmersion j.left ∧ x ∈ Set.range j.left ∧ Same A M P (fst U S') j

variable {A}

theorem Rep.of_isDual {B : Over S} [GrpObj B] {P : LB (A ⊗ B).left} (h : IsDual A B P) : Rep A (toUnit B) P where
  fam := ⟨h.isLB, h.additive⟩
  univ T t N hN := by
    obtain ⟨x, hx, hu⟩ := h.univ T N hN.isLB hN.add
    exact ⟨x, ⟨toUnit_unique _ _, hx⟩, fun y hy ↦ hu y hy.2⟩

omit [GrpObj A] in

theorem same_id_iff {T U : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (u : T ⟶ U) : Same A N M (𝟙 T) u ↔ LBIso N (ev M (fst A T) (snd A T ≫ u)) := by
  rw [Same, ← cls_eq_iff (pull_isLB hN _) (pull_isLB hM _), ← cls_eq_iff hN (pull_isLB hM _), cls_ev hN, evc,
    Category.comp_id, lift_fst_snd, Over.id_left, pull_id]

omit [GrpObj A] in

theorem same_iff {T U Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (y : Y ⟶ T) (u : Y ⟶ U) :
    Same A N M y u ↔ evc hN (fst A Y) (snd A Y ≫ y) = evc hM (fst A Y) (snd A Y ≫ u) :=
  (cls_eq_iff (pull_isLB hN _) (pull_isLB hM _)).symm

end GlobalTheory.DualCon
