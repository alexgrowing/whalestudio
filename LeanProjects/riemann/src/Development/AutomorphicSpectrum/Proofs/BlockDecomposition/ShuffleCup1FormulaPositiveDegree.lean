import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.ShMul

theorem val_predAbove {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((Fin.predAboveOrderHom i t : Fin (n + 1)) : ℕ) = if i.1 < t.1 then t.1 - 1 else t.1 := by
  show ((Fin.predAbove i t : Fin (n + 1)) : ℕ) = _
  rw [Fin.predAbove]
  split_ifs with h₁ h₂ h₂
  · simp
  · exact absurd (by simpa [Fin.lt_def] using h₁) h₂
  · exact absurd (by simpa [Fin.lt_def] using h₂) h₁
  · simp

theorem val_sI {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((sI i t : Fin (1 + 1)) : ℕ) = if i.1 < t.1 then 1 else 0 := by
  show ((if i.castSucc < t then (1 : Fin (1 + 1)) else 0 : Fin (1 + 1)) : ℕ) = _
  by_cases h : i.1 < t.1
  · rw [if_pos (by simpa [Fin.lt_def] using h), if_pos h]; rfl
  · rw [if_neg (by simpa [Fin.lt_def] using h), if_neg h]; rfl

macro "fin_order'" : tactic =>
  `(tactic| (apply Fin.ext; simp only [OrderHom.comp_coe, Function.comp_apply, OrderHom.id_coe, id_eq, val_dl, val_fr, cst_apply,
    val_sI, val_predAbove, Fin.val_succ, Fin.val_zero, Fin.val_one]; grind))

theorem shuffle_cup1_product_formula {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (n : ℕ)
    (u : Cn (box F) 1) (w : Cn (box F) (n + 1)) :
    Sh F (n + 1) (cup1 (box F) (n + 1) u w) =
      bv F OrderHom.id (cst 1 0) u * bv F (cst (n + 1) 1) OrderHom.id w -
        bv F (cst 1 0) (fr n) u * prB F (dl 0) (Sh F n w) := by
  have a1 : bv F (sI (0 : Fin (n + 1 + 1))) (Fin.predAboveOrderHom 0) (pr (box F) (fr (n + 1)) u) =
      bv F OrderHom.id (cst 1 0) u := by
    rw [bv_pr]
    exact bv_congr (fun t ↦ by fin_order') (fun t ↦ by fin_order') u
  have a2 : bv F (sI (0 : Fin (n + 1 + 1))) (Fin.predAboveOrderHom 0) (pr (box F) (dl 0) w) =
      bv F (cst (n + 1) 1) OrderHom.id w := by
    rw [bv_pr]
    exact bv_congr (fun t ↦ by fin_order') (fun t ↦ by fin_order') w
  have b1 : ∀ j : Fin (n + 1), bv F (sI j.succ) (Fin.predAboveOrderHom j.succ) (pr (box F) (fr (n + 1)) u) =
      bv F (cst 1 0) (fr n) u := fun j ↦ by
    rw [bv_pr]
    exact bv_congr (fun t ↦ by fin_order') (fun t ↦ by fin_order') u
  have b2 : ∀ j : Fin (n + 1), bv F (sI j.succ) (Fin.predAboveOrderHom j.succ) (pr (box F) (dl 0) w) =
      prB F (dl 0) (bv F (sI j) (Fin.predAboveOrderHom j) w) := fun j ↦ by
    rw [bv_pr, prB_bv]
    exact bv_congr (fun t ↦ by fin_order') (fun t ↦ by fin_order') w
  simp only [Sh, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, cup1_apply, map_mul, map_sum,
    map_smul]
  rw [Fin.sum_univ_succ]
  simp only [a1, a2, b1, b2, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Finset.mul_sum, mul_smul_comm]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [pow_succ]

end GlobalTheory.CompanionTheory.HopfC.ShMul
