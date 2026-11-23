import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.Prism

theorem prism_sum {R G : Type} [CommRing R] [AddCommGroup G] [Module R G] (N : ℕ) (a b : ℕ → ℕ → G)
    (h1 : ∀ k j, k < N → j ≤ k → a (k + 1) j = b k j)
    (h2 : ∀ k j, k < N → k < j → j < N + 1 → a k (j + 1) = b k j)
    (h3 : ∀ k, k < N → a k (k + 1) = a (k + 1) (k + 1)) :
    ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 2), ((-1 : R) ^ (i + j)) • a i j =
      a 0 0 - a N (N + 1) - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
  have row : ∀ i, i ≤ N → ∑ j ∈ Finset.range (N + 2), ((-1 : R) ^ (i + j)) • a i j =
      ∑ j ∈ Finset.range i, ((-1 : R) ^ (i + j)) • a i j + (a i i - a i (i + 1)) +
        ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) := by
    intro i hi
    have e1 := Finset.sum_range_add_sum_Ico (fun j ↦ ((-1 : R) ^ (i + j)) • a i j) (show i ≤ N + 2 by omega)
    have e2 : ∑ j ∈ Finset.Ico i (N + 2), ((-1 : R) ^ (i + j)) • a i j =
        ((-1 : R) ^ (i + i)) • a i i + ∑ j ∈ Finset.Ico i (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_Ico_add' (fun j ↦ ((-1 : R) ^ (i + j)) • a i j) i (N + 1) 1]
    have e3 : ∑ j ∈ Finset.Ico i (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) =
        ((-1 : R) ^ (i + (i + 1))) • a i (i + 1) +
          ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) :=
      Finset.sum_eq_sum_Ico_succ_bot (by omega) _
    have s1 : ((-1 : R) ^ (i + i)) = 1 := Even.neg_one_pow ⟨i, rfl⟩
    have s2 : ((-1 : R) ^ (i + (i + 1))) = -1 := by rw [← add_assoc, pow_succ, s1]; simp
    rw [← e1, e2, e3, s1, s2, one_smul, neg_smul, one_smul]
    abel
  rw [Finset.sum_congr rfl (fun i hi ↦ row i (by have := Finset.mem_range.1 hi; omega))]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have tL : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range i, ((-1 : R) ^ (i + j)) • a i j =
      - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [Finset.sum_range_succ', Finset.range_zero, Finset.sum_empty, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [h1 k j (Finset.mem_range.1 hk) (by have := Finset.mem_range.1 hj; omega), ← neg_smul]
    congr 1
    ring
  have tR : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) =
      - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.Ico (k + 1) (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [Finset.sum_range_succ, Finset.Ico_self, Finset.sum_empty, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have := Finset.mem_Ico.1 hj
    rw [h2 k j (Finset.mem_range.1 hk) (by omega) (by omega), ← neg_smul]
    congr 1
    ring
  have tD : ∑ i ∈ Finset.range (N + 1), (a i i - a i (i + 1)) = a 0 0 - a N (N + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_congr rfl (fun k hk ↦ by rw [h3 k (Finset.mem_range.1 hk)]),
      Finset.sum_range_sub' (fun i ↦ a i i)]
    abel
  have tS : ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (N + 1), ((-1 : R) ^ (k + j)) • b k j =
      ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ((-1 : R) ^ (k + j)) • b k j +
        ∑ k ∈ Finset.range N, ∑ j ∈ Finset.Ico (k + 1) (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have := Finset.mem_range.1 hk
    exact (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  rw [tL, tR, tD, tS]
  abel

section

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem val_sI {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((sI i t : Fin (1 + 1)) : ℕ) = if i.1 < t.1 then 1 else 0 := by
  show (((if i.castSucc < t then 1 else 0 : Fin (1 + 1))) : ℕ) = _
  by_cases h : i.1 < t.1
  · rw [if_pos (show i.castSucc < t from h), if_pos h]; rfl
  · rw [if_neg (show ¬ i.castSucc < t from h), if_neg h]; rfl

theorem val_pa {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((Fin.predAboveOrderHom i t : Fin (n + 1)) : ℕ) = if i.1 < t.1 then t.1 - 1 else t.1 := by
  show ((Fin.predAbove i t : Fin (n + 1)) : ℕ) = _
  rw [Fin.predAbove]
  by_cases h : i.1 < t.1
  · rw [dif_pos (show i.castSucc < t from h), if_pos h]; simp
  · rw [dif_neg (show ¬ i.castSucc < t from h), if_neg h]; simp

def aT {n : ℕ} (w : Cn (box F) (n + 1)) (i j : ℕ) : Bi F 1 (n + 1) :=
  if h : i < n + 2 ∧ j < n + 3 then
    bv F ((sI (⟨i, h.1⟩ : Fin (n + 1 + 1))).comp (dl (⟨j, h.2⟩ : Fin (n + 1 + 1 + 1))))
      ((Fin.predAboveOrderHom (⟨i, h.1⟩ : Fin (n + 1 + 1))).comp (dl (⟨j, h.2⟩ : Fin (n + 1 + 1 + 1)))) w
  else 0

def bT {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) : Bi F 1 (n + 1) :=
  if h : k < n + 1 ∧ j < n + 2 then
    bv F (sI (⟨k, h.1⟩ : Fin (n + 1)))
      ((dl (⟨j, h.2⟩ : Fin (n + 1 + 1))).comp (Fin.predAboveOrderHom (⟨k, h.1⟩ : Fin (n + 1)))) w
  else 0

variable {F}

theorem prism_term_lower_index {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) (hk : k < n + 1) (hj : j ≤ k) :
    aT F w (k + 1) j = bT F w k j := by
  rw [aT, bT, dif_pos (by omega), dif_pos (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem prism_term_upper_index {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) (hk : k < n + 1) (hkj : k < j) (hj : j < n + 2) :
    aT F w k (j + 1) = bT F w k j := by
  rw [aT, bT, dif_pos (by omega), dif_pos (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem prism_term_diagonal_equality {n : ℕ} (w : Cn (box F) (n + 1)) (k : ℕ) (hk : k < n + 1) :
    aT F w k (k + 1) = aT F w (k + 1) (k + 1) := by
  rw [aT, aT, dif_pos (by omega), dif_pos (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem aT_first {n : ℕ} (w : Cn (box F) (n + 1)) : aT F w 0 0 = prA F (dl 0) (S0 F (n + 1) w) := by
  rw [aT, dif_pos (by omega), S0, prA_bv]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl, cst_apply, Fin.val_zero]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl, Fin.val_zero, OrderHom.id_coe, id_eq]
    grind

theorem aT_last {n : ℕ} (w : Cn (box F) (n + 1)) :
    aT F w (n + 1) (n + 2) = prA F (dl 1) (S0 F (n + 1) w) := by
  rw [aT, dif_pos (by omega), S0, prA_bv]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl, cst_apply, Fin.val_zero, Fin.val_one]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl, OrderHom.id_coe, id_eq]
    grind

theorem Sh_dn_expand {n : ℕ} (w : Cn (box F) (n + 1)) :
    Sh F (n + 1) (dn (box F) (n + 1) w) =
      ∑ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 2), ((-1 : R) ^ (i + j)) • aT F w i j := by
  rw [dn_eq (n + 1)]
  simp only [Finset.sum_range, Sh, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum,
    map_smul, bv_pr, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [aT, dif_pos ⟨i.2, j.2⟩, pow_add, mul_comm]

theorem prB_Sh_expand {n : ℕ} (w : Cn (box F) (n + 1)) :
    ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) =
      ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 + 1), ((-1 : R) ^ (k + j)) • bT F w k j := by
  simp only [Finset.sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Sh, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum, map_smul, prB_bv]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [bT, dif_pos ⟨k.2, j.2⟩, smul_smul, pow_add, mul_comm]

theorem shuffle_coboundary_prism_identity {n : ℕ} (w : Cn (box F) (n + 1)) :
    Sh F (n + 1) (dn (box F) (n + 1) w) = prA F (dl 0) (S0 F (n + 1) w) - prA F (dl 1) (S0 F (n + 1) w) -
      ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) := by
  rw [Sh_dn_expand, prB_Sh_expand, ← aT_first, ← aT_last]
  exact prism_sum (n + 1) (aT F w) (bT F w) (fun k j hk hj ↦ prism_term_lower_index w k j hk hj)
    (fun k j hk hkj hj ↦ prism_term_upper_index w k j hk hkj hj) (fun k hk ↦ prism_term_diagonal_equality w k hk)

end

theorem Sh_dn : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (w : Cn (box F) (n + 1)), Sh F (n + 1) (dn (box F) (n + 1) w) = prA F (dl 0) (S0 F (n + 1) w) - prA F (dl 1) (S0 F (n + 1) w) - ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) :=
  fun _ _ w ↦ shuffle_coboundary_prism_identity w

end GlobalTheory.CompanionTheory.HopfC.Prism
