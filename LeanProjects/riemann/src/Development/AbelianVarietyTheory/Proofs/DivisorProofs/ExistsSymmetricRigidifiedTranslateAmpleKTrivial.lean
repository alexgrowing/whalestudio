import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundle
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymTranslate

open GlobalTheory.CechPic (cls)

theorem exists_sym_translate : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (b : 𝟙_ _ ⟶ B), IsAbelianScheme B → M.IsLB → RelAmple B M → KTriv B M → (∃ t : LB.Gen (Theta B M), t.IsGen) → LBIso (M.pull (ι[B]).left) (M.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left) → ∃ L : LB B.left, L.IsLB ∧ Rigidified B L ∧ Out.Sym B L ∧ RelAmple B L ∧ KTriv B L ∧ LBIso (abelian₂ B L) (abelian₂ B M) := by
  intro A _ _ _ B _ _ M b hB hM hamp hK hT hiso
  have := hB.proper
  obtain ⟨c, hc⟩ := hT
  have hL' : (GlobalTheory.RigidTranslate.rigTransl M b).IsLB := LB.isLB_linComb hM _ _
  refine ⟨GlobalTheory.RigidTranslate.rigTransl M b, hL', GlobalTheory.RigidTranslate.rigidified_rigTransl hM, ?_,
    GlobalTheory.RigidTranslate.relAmple_rigTransl_of_section b hM hamp, GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ B M hM b hK, ?_⟩
  · have h2 : CechPic.pull (GrpObj.inv : B ⟶ B).left (cls M hM) =
        CechPic.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left (cls M hM) :=
      (CechPic.cls_eq_iff (pull_isLB hM _) (pull_isLB hM _)).2 hiso
    have h3 := congrArg (CechPic.pull (𝟙 B * (toUnit B ≫ b)⁻¹).left) h2
    rw [← CechPic.pull_comp, ← CechPic.pull_comp, ← Over.comp_left, ← Over.comp_left] at h3
    have e1 : (𝟙 B * (toUnit B ≫ b)⁻¹) ≫ (GrpObj.inv : B ⟶ B) =
        (GrpObj.inv : B ⟶ B) ≫ (𝟙 B * (toUnit B ≫ b)) := by
      rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv, inv_inv,
        Hom.inv_def, Category.id_comp]
    have e2 : (𝟙 B * (toUnit B ≫ b)⁻¹) ≫ ((toUnit B ≫ b ^ 2) * 𝟙 B) = 𝟙 B * (toUnit B ≫ b) := by
      rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, MonObj.comp_pow, sq,
        _root_.mul_comm (𝟙 B), _root_.mul_comm (𝟙 B), _root_.mul_assoc, mul_inv_cancel_left]
    rw [e1, e2, Over.comp_left, CechPic.pull_comp] at h3
    have e3 : (GrpObj.inv : B ⟶ B).left ≫ (toUnit B ≫ b).left = (toUnit B ≫ b).left := by
      rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    have h4 : cls _ hL' = CechPic.pull (𝟙 B * (toUnit B ≫ b)).left (cls M hM) -
        CechPic.pull (toUnit B ≫ b).left (cls M hM) := by
      rw [CechPic.cls_linComb hM, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
      rfl
    refine GlobalTheory.RigSymSubring.sym_of_cls hL' ?_
    rw [h4, map_sub, h3, ← CechPic.pull_comp, e3]
  · have hΛ : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
    refine (CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) hΛ).1
      (((CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) (pull_isLB hΛ _)).2
        (GlobalTheory.RigidTranslate.lam_rigTransl hM c hc)).trans ?_)
    rw [CechPic.cls_pull hΛ]
    exact CechPic.pull_id _

end GlobalTheory.SymTranslate
