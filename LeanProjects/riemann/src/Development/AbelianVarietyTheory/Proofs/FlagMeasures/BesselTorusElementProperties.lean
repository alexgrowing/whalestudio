import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

namespace GlobalTheory.ThA.TorusElt

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix

noncomputable section

def dg (k r : ℕ) (α : ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then α ^ (r - i.val) else if i.val ≤ r + k then 1 else ((star α) ^ (i.val - (r + k)))⁻¹

theorem aT_eq (k r : ℕ) (α : ℂ) : aT k r α = Matrix.diagonal (dg k r α) := rfl

variable {k r : ℕ} {α : ℂ}

theorem dg_ne (hα : α ≠ 0) (i : Fin (2 * r + k + 1)) : dg k r α i ≠ 0 := by
  unfold dg
  split_ifs
  · exact pow_ne_zero _ hα
  · exact one_ne_zero
  · exact inv_ne_zero (pow_ne_zero _ (star_ne_zero.mpr hα))

theorem dg_mid (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : dg k r α i = 1 := by
  unfold dg
  rw [if_neg (Nat.not_lt.mpr h1), if_pos h2]

theorem dg_eI (a : Fin r) : dg k r α (eI k r a) = α ^ (r - a.val) := by
  have h : (eI k r a).val < r := a.isLt
  unfold dg
  rw [if_pos h]
  rfl

theorem aT_inv (hα : α ≠ 0) : (aT k r α)⁻¹ = Matrix.diagonal (fun i => (dg k r α i)⁻¹) := by
  rw [aT_eq]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (dg_ne hα i)

theorem conj_apply (hα : α ≠ 0) (n : B.Mat k r) (i j : Fin (2 * r + k + 1)) :
    (aT k r α * n * (aT k r α)⁻¹) i j = dg k r α i * n i j * (dg k r α j)⁻¹ := by
  rw [aT_inv hα, aT_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem conj_apply' (hα : α ≠ 0) (n : B.Mat k r) (i j : Fin (2 * r + k + 1)) :
    ((aT k r α)⁻¹ * n * aT k r α) i j = (dg k r α i)⁻¹ * n i j * dg k r α j := by
  rw [aT_inv hα, aT_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]

private lemma star_dg_mul_dg_eq_one_of_Hpk_ne_zero (hα : α ≠ 0) (i j : Fin (2 * r + k + 1)) (h : Hpk k r i j ≠ 0) :
    star (dg k r α i) * dg k r α j = 1 := by
  have hs : star α ≠ 0 := star_ne_zero.mpr hα
  unfold Hpk at h
  split_ifs at h with h1 h2 h3
  · have hj1 : ¬ j.val < r := by omega
    have hj2 : ¬ j.val ≤ r + k := by omega
    have he : j.val - (r + k) = r - i.val := by omega
    unfold dg
    rw [if_pos h1.1, if_neg hj1, if_neg hj2, he, star_pow]
    exact mul_inv_cancel₀ (pow_ne_zero _ hs)
  · have hi1 : ¬ i.val < r := by omega
    have hi2 : ¬ i.val ≤ r + k := by omega
    have he : i.val - (r + k) = r - j.val := by omega
    unfold dg
    rw [if_neg hi1, if_neg hi2, if_pos h2.1, he, star_inv₀, star_pow, star_star]
    exact inv_mul_cancel₀ (pow_ne_zero _ hα)
  · obtain ⟨hr, hk, hij⟩ := h3
    rw [← hij, dg_mid i hr hk, star_one, one_mul]
  · obtain ⟨hr, hk, hij⟩ := h3
    rw [← hij, dg_mid i hr hk, star_one, one_mul]
  · exact absurd rfl h

theorem aT_mem (hα : α ≠ 0) : aT k r α ∈ B.GV k r := by
  show (aT k r α)ᴴ * Hpk k r * aT k r α = Hpk k r
  ext i j
  rw [aT_eq, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  by_cases h0 : Hpk k r i j = 0
  · rw [h0, mul_zero, zero_mul]
  · rw [mul_comm (star (dg k r α i)) _, mul_assoc, star_dg_mul_dg_eq_one_of_Hpk_ne_zero hα i j h0, mul_one]

theorem aT_comm {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) :
    aT k r α * h = h * aT k r α := by
  have hb := WeylGroupFacts.uw_block hh
  rw [aT_eq]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [hb.1 i j hj]
    split_ifs with hij
    · rw [hij, mul_one, one_mul]
    · rw [mul_zero, zero_mul]
  · by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hb.2 i j hi]
      split_ifs with hij
      · rw [hij, mul_one, one_mul]
      · rw [mul_zero, zero_mul]
    · rw [dg_mid i (by omega) (by omega), dg_mid j (by omega) (by omega), one_mul, mul_one]

private lemma conj_mem_lemma (hα : α ≠ 0) (n : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (h : n i j = if i = j then 1 else 0) :
    (aT k r α * n * (aT k r α)⁻¹) i j = if i = j then 1 else 0 := by
  rw [conj_apply hα, h]
  split_ifs with hij
  · rw [hij, mul_one]
    exact mul_inv_cancel₀ (dg_ne hα j)
  · rw [mul_zero, zero_mul]

theorem conj_mem (hα : α ≠ 0) {n : B.Mat k r} (hn : n ∈ Nset k r) :
    aT k r α * n * (aT k r α)⁻¹ ∈ Nset k r := by
  simp only [Nset, Set.mem_setOf_eq] at hn ⊢
  obtain ⟨hU, h2, h3⟩ := hn
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (aT_mem hα) hU) (WeylGroupFacts.uh_inv (aT_mem hα)), fun a i hai => ?_,
    fun i j hj1 hj2 hi => ?_⟩
  · exact conj_mem_lemma hα n _ _ (h2 a i hai)
  · exact conj_mem_lemma hα n _ _ (h3 i j hj1 hj2 hi)

private lemma aT_inv_mul_mul_aT_apply_eq_one_apply (hα : α ≠ 0) (n : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (h : n i j = if i = j then 1 else 0) :
    ((aT k r α)⁻¹ * n * aT k r α) i j = if i = j then 1 else 0 := by
  rw [conj_apply' hα, h]
  split_ifs with hij
  · rw [hij, mul_one]
    exact inv_mul_cancel₀ (dg_ne hα j)
  · rw [mul_zero, zero_mul]

theorem conj_mem' (hα : α ≠ 0) {n : B.Mat k r} (hn : n ∈ Nset k r) :
    (aT k r α)⁻¹ * n * aT k r α ∈ Nset k r := by
  simp only [Nset, Set.mem_setOf_eq] at hn ⊢
  obtain ⟨hU, h2, h3⟩ := hn
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv (aT_mem hα)) hU) (aT_mem hα), fun a i hai => ?_,
    fun i j hj1 hj2 hi => ?_⟩
  · exact aT_inv_mul_mul_aT_apply_eq_one_apply hα n _ _ (h2 a i hai)
  · exact aT_inv_mul_mul_aT_apply_eq_one_apply hα n _ _ (h3 i j hj1 hj2 hi)

theorem ell_conj (hα : α ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (n : B.Mat k r) :
    ell k r z (aT k r α * n * (aT k r α)⁻¹) = α * ell k r z n := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha0 := a.isLt
  split_ifs with h
  · rw [conj_apply hα, dg_eI, dg_eI]
    have he : r - a.val = (r - (a.val + 1)) + 1 := by omega
    have key : ∀ (m : ℕ) (x : ℂ), α ^ (m + 1) * x * (α ^ m)⁻¹ = α * x := by
      intro m x
      rw [pow_succ, show α ^ m * α * x = α * x * α ^ m by ring, mul_inv_cancel_right₀ (pow_ne_zero _ hα)]
    rw [he]
    exact key _ _
  · have ha : r - a.val = 1 := by omega
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conj_apply hα, dg_eI, ha, pow_one]
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj]
      simp
    · rw [dg_mid j (by omega) (by omega), inv_one, mul_one, mul_assoc]

theorem aT_fvec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (b : Fin (r + 1)) :
    aT k r α *ᵥ fvec k r z b = α ^ (r - b.val) • fvec k r z b := by
  funext i
  have hb0 := b.isLt
  rw [aT_eq, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  unfold fvec
  split_ifs with hb
  · by_cases hi : i = eI k r ⟨b.val, hb⟩
    · rw [hi, dg_eI]
    · rw [bvec, Pi.single_eq_of_ne hi, mul_zero, mul_zero]
  · have h0 : r - b.val = 0 := by omega
    rw [h0, pow_zero, one_mul]
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hz i hi, mul_zero]
    · rw [dg_mid i (by omega) (by omega), one_mul]

theorem herm_unit {ι : Type*} [Fintype ι] [DecidableEq ι] {H g : Matrix ι ι ℂ} (hg : g ∈ UH H) (v w : ι → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem zhat_conj (hα : α ≠ 0) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (g : B.Mat k r) (a b : Fin (r + 1)) :
    Zhat k r z z' ((aT k r α)⁻¹ * g * aT k r α) a b =
      (star α) ^ (r - a.val) * α ^ (r - b.val) * Zhat k r z z' g a b := by
  have hA := aT_mem (k := k) (r := r) hα
  have hU : (aT k r α)⁻¹ ∈ UH (Hpk k r) := WeylGroupFacts.uh_inv hA
  have hdet : IsUnit (aT k r α).det := WeylGroupFacts.isUnit_of_uh hA
  have h1 : fvec k r z a = (aT k r α)⁻¹ *ᵥ (α ^ (r - a.val) • fvec k r z a) := by
    rw [← aT_fvec hz a, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  simp only [Zhat]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, aT_fvec hz' b]
  conv_lhs => rw [h1]
  rw [herm_unit hU]
  simp only [herm, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, star_pow]
  ring

theorem norm_pow_eq (α : ℂ) (m : ℕ) : ((‖α‖ ^ (2 * m) : ℝ) : ℂ) = (star α) ^ m * α ^ m := by
  rw [pow_mul, Complex.sq_norm, Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self, mul_pow]
  rfl

theorem bigCell_conj (hα : α ≠ 0) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (aT k r α)⁻¹ * bigCell k r c μ * aT k r α =
      bigCell k r (fun a => ((‖α‖ ^ (2 * (r - a.val)) : ℝ) : ℂ) * c a) μ := by
  ext i j
  rw [conj_apply' hα]
  unfold bigCell
  have hjl := j.isLt
  by_cases hj : j.val < r
  · have hdj : dg k r α j = α ^ (r - j.val) := by
      unfold dg
      rw [if_pos hj]
    by_cases hi : i = esI k r ⟨j.val, hj⟩
    · have hiv : i.val = 2 * r + k - j.val := by
        rw [hi]
        rfl
      have hi1 : ¬ i.val < r := by omega
      have hi2 : ¬ i.val ≤ r + k := by omega
      have he : i.val - (r + k) = r - j.val := by omega
      have hdi : dg k r α i = ((star α) ^ (r - j.val))⁻¹ := by
        unfold dg
        rw [if_neg hi1, if_neg hi2, he]
      simp only [dif_pos hj, if_pos hi]
      rw [hdi, hdj, inv_inv, norm_pow_eq]
      ring
    · simp only [dif_pos hj, if_neg hi, mul_zero, zero_mul]
  · by_cases hj2 : j.val ≤ r + k
    · by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · simp only [dif_neg hj, dif_pos hj2, dif_pos hi]
        rw [dg_mid i hi.1 hi.2, dg_mid j (by omega) hj2, inv_one, one_mul, mul_one]
      · simp only [dif_neg hj, dif_pos hj2, dif_neg hi, mul_zero, zero_mul]
    · by_cases hi : i.val = 2 * r + k - j.val
      · have hi1 : i.val < r := by omega
        have he : j.val - (r + k) = r - i.val := by omega
        have hm : r - (2 * r + k - j.val) = r - i.val := by omega
        have hdi : dg k r α i = α ^ (r - i.val) := by
          unfold dg
          rw [if_pos hi1]
        have hdj : dg k r α j = ((star α) ^ (r - i.val))⁻¹ := by
          unfold dg
          rw [if_neg hj, if_neg hj2, he]
        simp only [dif_neg hj, dif_neg hj2, if_pos hi]
        rw [hm, norm_pow_eq, hdi, hdj]
        simp only [star_mul', star_pow, star_star, mul_inv]
        ring
      · simp only [dif_neg hj, dif_neg hj2, if_neg hi, mul_zero, zero_mul]

theorem torusElt : ∀ (k r : ℕ) (α : ℂ), α ≠ 0 → aT k r α ∈ B.GV k r ∧ (∀ z, inWb k r z → (∀ h ∈ UWset k r z, aT k r α * h = h * aT k r α) ∧ ∀ n ∈ Nset k r, aT k r α * n * (aT k r α)⁻¹ ∈ Nset k r ∧ (aT k r α)⁻¹ * n * aT k r α ∈ Nset k r ∧ ell k r z (aT k r α * n * (aT k r α)⁻¹) = α * ell k r z n) ∧ (∀ z z', inWb k r z → inWb k r z' → ∀ (g : B.Mat k r) (a b : Fin (r + 1)), Zhat k r z z' ((aT k r α)⁻¹ * g * aT k r α) a b = (star α) ^ (r - a.val) * α ^ (r - b.val) * Zhat k r z z' g a b) ∧ ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (aT k r α)⁻¹ * bigCell k r c μ * aT k r α = bigCell k r (fun a => ((‖α‖ ^ (2 * (r - a.val)) : ℝ) : ℂ) * c a) μ := by
  intro k r α hα
  exact ⟨aT_mem hα, fun z hz => ⟨fun h hh => aT_comm hh, fun n hn =>
    ⟨conj_mem hα hn, conj_mem' hα hn, ell_conj hα hz n⟩⟩,
    fun z z' hz hz' g a b => zhat_conj hα hz hz' g a b, fun c μ => bigCell_conj hα c μ⟩

end

end GlobalTheory.ThA.TorusElt
