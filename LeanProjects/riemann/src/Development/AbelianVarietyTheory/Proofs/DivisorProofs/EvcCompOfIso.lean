import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

theorem evc_comp_of_iso {S : Scheme.{0}} {A B' B Y : Over S} (j : B' ⟶ B) {P : LB (A ⊗ B).left} (hP : P.IsLB)
    {Q : LB (A ⊗ B').left} (hQ : Q.IsLB) (h : LBIso (P.pull (A ◁ j).left) Q) (a : Y ⟶ A) (u : Y ⟶ B') :
    evc hP a (u ≫ j) = evc hQ a u := by
  have e : cls Q hQ = CechPic.pull (A ◁ j).left (cls P hP) :=
    ((cls_eq_iff (pull_isLB hP _) hQ).2 h).symm.trans (cls_pull hP _ _)
  rw [evc, evc, e, ← pull_comp, ← Over.comp_left, lift_whiskerLeft]

end GlobalTheory.DualCon.ProdGlue
