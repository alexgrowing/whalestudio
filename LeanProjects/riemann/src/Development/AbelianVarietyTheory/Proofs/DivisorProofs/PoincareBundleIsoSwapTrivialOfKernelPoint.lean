import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.CechPic

namespace GlobalTheory.AbDual

theorem lbIso_swap_and_triv_of_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (l : A ⟶ B), LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) → LBIso (GlobalTheory.AbDual.ev P (fst A A) (snd A A ≫ 𝟙 A)) (GlobalTheory.AbDual.ev (GlobalTheory.AbDual.swap P₀) (fst A A ≫ l) (snd A A)) ∧ ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen := by
  intro k _ A B _ _ P₀ hD P hP hsym l hl
  have hP₀ := hD.isLB
  have e₁ : cls P hP = evc hP (snd A A) (fst A A) :=
    (CechPic.cls_eq_iff hP (pull_isLB hP _)).2 hsym
  have e₂ : cls P hP = evc hP₀ (fst A A) (snd A A ≫ l) :=
    (CechPic.cls_eq_iff hP (pull_isLB hP₀ _)).2 hl
  have key : ∀ (Y : Over (Sp k)) (a b : Y ⟶ A), evc hP a b = evc hP₀ b (a ≫ l) := by
    intro Y a b
    have h1 : evc hP a b = CechPic.pull (lift a b).left (evc hP (snd A A) (fst A A)) := by
      rw [← e₁]; rfl
    rw [h1, pull_evc, lift_snd, lift_fst]
    change CechPic.pull (lift b a).left (cls P hP) = _
    rw [e₂, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨?_, fun T x hx => ?_⟩
  · refine (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _)).1 ?_
    rw [cls_ev hP, cls_ev (pull_isLB hP₀ _), evc_swap hP₀, key, Category.comp_id]
  · show Triv _
    rw [triv_ev_iff hP, key, Category.assoc, hx, MonObj.comp_one]
    exact evc_one_right hP₀ hD.zero _

end GlobalTheory.AbDual
