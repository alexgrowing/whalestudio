import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamA

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}}

section Biadd

variable {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left} (hD : IsDual A B P)
  (hD' : IsDual B A (swap P)) {Y : Over S}

include hD in
theorem evc_mul_left (a a' : Y ⟶ A) (b : Y ⟶ B) :
    evc hD.isLB (a * a') b = evc hD.isLB a b + evc hD.isLB a' b :=
  (isAdditive_iff hD.isLB).1 hD.additive Y a a' b

include hD hD' in
theorem evc_mul_right (a : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hD.isLB a (b * b') = evc hD.isLB a b + evc hD.isLB a b' := by
  rw [← evc_swap hD.isLB hD'.isLB, (isAdditive_iff hD'.isLB).mp hD'.additive Y b b' a, evc_swap, evc_swap]

include hD in
theorem evc_one_l (b : Y ⟶ B) : evc hD.isLB (1 : Y ⟶ A) b = 0 := hD.additive.evc_one hD.isLB b

include hD in
theorem evc_one_r (a : Y ⟶ A) : evc hD.isLB a (1 : Y ⟶ B) = 0 := evc_one_right hD.isLB hD.zero a

include hD hD' in
theorem evc_inv_inv (a : Y ⟶ A) (b : Y ⟶ B) : evc hD.isLB a⁻¹ b⁻¹ = evc hD.isLB a b := by
  have hl : evc hD.isLB a⁻¹ b⁻¹ = - evc hD.isLB a b⁻¹ := by
    have h := evc_mul_left hD a⁻¹ a b⁻¹
    rw [_root_.inv_mul_cancel, evc_one_l hD] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hr : evc hD.isLB a b⁻¹ = - evc hD.isLB a b := by
    have h := evc_mul_right hD hD' a b⁻¹ b
    rw [_root_.inv_mul_cancel, evc_one_r hD] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  rw [hl, hr, neg_neg]

end Biadd

section abelian₂

variable {S' : Scheme.{0}} {G G' T : Over S'} [GrpObj G] [GrpObj G']

def lamHom (x y : T ⟶ G) : Pic G.left →+ Pic T.left :=
  pull (x * y).left - pull x.left - pull y.left + pull (1 : T ⟶ G).left

theorem lam_eq_lamHom (c : Pic G.left) (x y : T ⟶ G) : lam c x y = lamHom x y c := by
  simp [lam, lamHom]

theorem lam_pull_pt (φ : G ⟶ G') (c : Pic G'.left) (x y : T ⟶ G) (hm : (x * y) ≫ φ = (x ≫ φ) * (y ≫ φ))
    (h1 : (1 : T ⟶ G) ≫ φ = 1) : lam (pull φ.left c) x y = lam c (x ≫ φ) (y ≫ φ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, hm, h1]

end abelian₂

section Fib

variable {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

theorem map_mul_pt {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f] {T : Over (Sp Ω)}
    (x y : T ⟶ (Over.pullback s).obj G) :
    (x * y) ≫ (Over.pullback s).map f = (x ≫ (Over.pullback s).map f) * (y ≫ (Over.pullback s).map f) := by
  apply toBase_injective s
  rw [toBase_map, toBase_mul, toBase_mul, toBase_map, toBase_map, MonObj.mul_comp]

theorem map_one_pt {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f] {T : Over (Sp Ω)} :
    (1 : T ⟶ (Over.pullback s).obj G) ≫ (Over.pullback s).map f = 1 := by
  apply toBase_injective s G'
  rw [toBase_map, toBase_one, toBase_one, MonObj.one_comp]

end Fib

end PositivityTheory.PrwZar
