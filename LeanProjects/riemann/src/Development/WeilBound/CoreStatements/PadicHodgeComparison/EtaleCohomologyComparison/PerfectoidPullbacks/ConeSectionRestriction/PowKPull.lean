import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem powK_pull {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {C : Type 1} [Category.{0} C]
    (g : C ⥤ Thick (smFun X q)) (c : HdR q 2) (z : CH.Cn (CH.modF (g ⋙ thA (smFun X q))) 2) (hz : CH.d _ 2 z = 0)
    (hcz : (CH.cx _).cls z hz = (CH.Mor.restrict (O (smFun X q)) g).pull 2 c) (k : ℕ) :
    ∃ h, (CH.cx _).cls (cupPowC (g ⋙ thA (smFun X q)) z k) h = (CH.Mor.restrict (O (smFun X q)) g).pull (2 * k) (powK q c k) := by
  induction k with
  | zero =>
    change ∃ h : CH.d (CH.modF (g ⋙ thA (smFun X q))) 0 (cupPowC (g ⋙ thA (smFun X q)) z 0) = 0,
      (CH.cx (CH.modF (g ⋙ thA (smFun X q)))).cls (n := 0) (cupPowC (g ⋙ thA (smFun X q)) z 0) h =
        (CH.Mor.restrict (O (smFun X q)) g).hom.mapH 0 (CH.oneH (thA (smFun X q)))
    have h0 : CH.d (CH.modF (g ⋙ thA (smFun X q))) 0 (cupPowC (g ⋙ thA (smFun X q)) z 0) = 0 := by
      funext s
      simp only [CH.d, cupPowC, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_two]
      simp [CH.modF]
    refine ⟨h0, ?_⟩
    unfold CH.oneH
    exact (CrystallineSemistableComparison.P.mapH_cls (CH.Mor.restrict (O (smFun X q)) g).hom 0
      (fun s => (1 : (thA (smFun X q)).obj (s.obj (Fin.last 0)))) _ (by exact h0)).symm
  | succ k ih =>
    obtain ⟨hk, ek⟩ := ih
    obtain ⟨hc, ec⟩ := CrystallineSemistableComparison.P.cup_cls (CH.mulP (g ⋙ thA (smFun X q))) (show 2 * k + 2 = 2 * (k + 1) by omega)
      (cupPowC (g ⋙ thA (smFun X q)) z k) z hk hz
    refine ⟨hc, ?_⟩
    have key := CrystallineSemistableComparison.P.cup_pull (CH.mulP (thA (smFun X q))) (CH.mulP (g ⋙ thA (smFun X q))) g
      (fun _ => LinearMap.id) (fun _ => LinearMap.id) (fun _ => LinearMap.id)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (show 2 * k + 2 = 2 * (k + 1) by omega) (powK q c k) c
    change _ = (CH.Mor.restrict (O (smFun X q)) g).pull (2 * (k + 1))
      ((CH.mulP (thA (smFun X q))).cup (show 2 * k + 2 = 2 * (k + 1) by omega) (powK q c k) c)
    refine (ec.symm.trans ?_).trans key.symm
    rw [ek, hcz]
    rfl

end CrystallineSemistableComparison.Pb
