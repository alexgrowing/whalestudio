import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CechPicMul

open Classical in

def cl {X : Scheme.{0}} (L : LB X) : Multiplicative (CechPic.Pic X) :=
  if h : L.IsLB then Multiplicative.ofAdd (CechPic.cls L h) else 1

theorem cl_eq {X : Scheme.{0}} {L : LB X} (h : L.IsLB) : cl L = Multiplicative.ofAdd (CechPic.cls L h) := dif_pos h

theorem exists_picardGroup : ∃ (Pic : Scheme.{0} → Type 1) (_ : ∀ X, CommGroup (Pic X)) (cl : ∀ {X : Scheme.{0}}, LB X → Pic X) (pl : ∀ {X Y : Scheme.{0}}, (Y ⟶ X) → (Pic X →* Pic Y)),
  (∀ (X : Scheme.{0}) (L M : LB X), L.IsLB → M.IsLB → (cl L = cl M ↔ LBIso L M)) ∧ (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → (cl L = 1 ↔ ∃ t : LB.Gen L, t.IsGen)) ∧
  (∀ (X : Scheme.{0}) (c : Pic X), pl (𝟙 X) c = c) ∧ (∀ (X Y Z : Scheme.{0}) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Pic X), pl (g ≫ f) c = pl g (pl f c)) ∧
  (∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ), (LB.LinComb L φ ε).IsLB ∧ cl (LB.LinComb L φ ε) = ∏ k, pl (φ k) (cl L) ^ ε k) ∧
  ∀ (X : Scheme.{0}) (L M : LB X), L.IsLB → M.IsLB → (LB.div M L).IsLB ∧ cl (LB.div M L) = cl M / cl L := by
  refine ⟨fun X => Multiplicative (CechPic.Pic X), fun X => inferInstance, cl,
    fun f => AddMonoidHom.toMultiplicative (CechPic.pull f), fun X L M hL hM => ?_, fun X L hL => ?_,
    fun X c => CechPic.pull_id c.toAdd, fun X Y Z f g c => CechPic.pull_comp g f c.toAdd,
    fun X Y L hL I _ φ ε => ⟨LB.isLB_linComb hL φ ε, ?_⟩, fun X L M hL hM => ⟨LB.isLB_div hM hL, ?_⟩⟩
  · beta_reduce
    rw [cl_eq hL, cl_eq hM]
    exact CechPic.cls_eq_iff hL hM
  · beta_reduce
    rw [cl_eq hL]
    exact CechPic.cls_eq_zero_iff hL
  · beta_reduce
    rw [cl_eq (LB.isLB_linComb hL φ ε), cl_eq hL, CechPic.cls_linComb hL, ofAdd_sum]
    rfl
  · beta_reduce
    rw [cl_eq (LB.isLB_div hM hL), cl_eq hL, cl_eq hM, CechPic.cls_div hM hL]
    rfl

end GlobalTheory.CechPicMul
