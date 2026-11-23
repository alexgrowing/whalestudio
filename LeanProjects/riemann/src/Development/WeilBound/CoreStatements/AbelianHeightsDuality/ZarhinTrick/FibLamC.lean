import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

omit [GrpObj B] in

theorem lam_cL_pt {P : LB (A ⊗ B).left} (hP : P.IsLB) (l : A ⟶ B) (L : LB ((Over.pullback s).obj A).left)
    (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {T : Over (Sp Ω)} (p q : T ⟶ (Over.pullback s).obj A) :
    lam (cls L hL) p q = evc hP (toBase A s p) (toBase A s q ≫ l) := by
  have hLam := GlobalTheory.FullSiegel.isLB_lam (G := (Over.pullback s).obj A) hL
  have hE : (ev P (fst A A) (snd A A ≫ l)).IsLB := LB.isLB_pull hP _
  have hM := LB.isLB_pull hE (sqToBase A s)
  have hc : cls (abelian₂ ((Over.pullback s).obj A) L) hLam = cls _ hM := (cls_eq_iff hLam hM).mpr (LBIso.symm e)
  rw [← GlobalTheory.FullSiegel.cls_lam_pull hL p q, cls_pull hLam, hc, cls_pull hE, cls_ev hP]
  have hw : sqToBase A s = Over.Hom.left (lift (toBase A s (fst ((Over.pullback s).obj A) ((Over.pullback s).obj A)))
      (toBase A s (snd ((Over.pullback s).obj A) ((Over.pullback s).obj A)))) := rfl
  rw [hw, pull_evc, lift_fst, lift_snd_assoc]
  have e1 := toBase_comp s A (lift p q) (fst _ _)
  have e2 := toBase_comp s A (lift p q) (snd _ _)
  rw [lift_fst] at e1
  rw [lift_snd] at e2
  rw [e1, e2, Category.assoc (Over.homMk _ _) _ l, ← pull_evc]
  rfl

theorem pull_phiP {P : LB (A ⊗ B).left} (hP : P.IsLB) {T : Over (Sp Ω)}
    (v : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) (ij : Fin 4 × Fin 4) :
    pull v.left (pull (phiP s ij) (cls P hP)) =
      evc hP (toBase _ s v ≫ prj _ ij.1 ≫ fst A B) (toBase _ s v ≫ prj _ ij.2 ≫ snd A B) := by
  have e1 := toBase_comp s (G4 (A ⊗ B)) v (𝟙 _)
  rw [Category.comp_id] at e1
  rw [evc, e1, ← comp_lift, Category.assoc, Over.comp_left, pull_comp]
  rfl

end PositivityTheory.PrwZar
