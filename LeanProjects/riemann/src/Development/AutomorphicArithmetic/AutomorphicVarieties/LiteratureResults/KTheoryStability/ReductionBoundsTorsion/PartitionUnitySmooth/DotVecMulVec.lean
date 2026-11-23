import Mathlib

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.TraceLipschitz

theorem cs_pd {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ} (hP : P.PosDef) (a b : ι → ℂ) :
    ‖star a ⬝ᵥ (P *ᵥ b)‖ ^ 2 ≤ (star a ⬝ᵥ (P *ᵥ a)).re * (star b ⬝ᵥ (P *ᵥ b)).re := by
  let _ := P.toSeminormedAddCommGroup hP.posSemidef
  let _ := P.toInnerProductSpace hP.posSemidef
  have cs := inner_mul_inner_self_le (𝕜 := ℂ) a b
  have e1 : (inner ℂ a b : ℂ) = star a ⬝ᵥ (P *ᵥ b) := by
    change (P *ᵥ b) ⬝ᵥ star a = _
    rw [dotProduct_comm]
  have e2 : (inner ℂ b a : ℂ) = star (star a ⬝ᵥ (P *ᵥ b)) := by
    rw [← e1]; exact (inner_conj_symm (𝕜 := ℂ) b a).symm
  have e3 : (inner ℂ a a : ℂ) = star a ⬝ᵥ (P *ᵥ a) := by
    change (P *ᵥ a) ⬝ᵥ star a = _
    rw [dotProduct_comm]
  have e4 : (inner ℂ b b : ℂ) = star b ⬝ᵥ (P *ᵥ b) := by
    change (P *ᵥ b) ⬝ᵥ star b = _
    rw [dotProduct_comm]
  rw [e1, e2, e3, e4, norm_star] at cs
  simp only [RCLike.re_to_complex] at cs
  rw [sq]
  exact cs

theorem dot_vecMulVec {ι : Type*} [Fintype ι] (a z : ι → ℂ) :
    (star z ⬝ᵥ (vecMulVec a (star a) *ᵥ z)).re = ‖star z ⬝ᵥ a‖ ^ 2 := by
  have key : star z ⬝ᵥ (vecMulVec a (star a) *ᵥ z) = (star z ⬝ᵥ a) * star (star z ⬝ᵥ a) := by
    simp only [dotProduct, mulVec, vecMulVec_apply, Pi.star_apply, star_sum, star_mul', star_star]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key, Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem st_lip : ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ,
    |Real.smoothTransition a - Real.smoothTransition b| ≤ K * |a - b| := by
  obtain ⟨K, hK⟩ := (Real.smoothTransition.contDiff (n := 1)).contDiffOn.exists_lipschitzOnWith
    (s := Set.Icc (0 : ℝ) 1) (by simp) (convex_Icc 0 1) isCompact_Icc
  refine ⟨K, K.2, fun a b => ?_⟩
  have hp : ∀ x : ℝ, Real.smoothTransition (max 0 (min x 1)) = Real.smoothTransition x := by
    intro x
    by_cases h0 : x ≤ 0
    · rw [show max 0 (min x 1) = (0 : ℝ) by rw [min_eq_left (by linarith), max_eq_left h0],
        Real.smoothTransition.zero_of_nonpos le_rfl, Real.smoothTransition.zero_of_nonpos h0]
    by_cases h1 : 1 ≤ x
    · rw [show max 0 (min x 1) = (1 : ℝ) by rw [min_eq_right h1, max_eq_right zero_le_one],
        Real.smoothTransition.one_of_one_le le_rfl, Real.smoothTransition.one_of_one_le h1]
    · push Not at h0 h1
      rw [min_eq_left h1.le, max_eq_right h0.le]
  have hm : ∀ x : ℝ, max 0 (min x 1) ∈ Set.Icc (0 : ℝ) 1 := fun x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  rw [← hp a, ← hp b]
  have h1 := hK.dist_le_mul _ (hm a) _ (hm b)
  rw [Real.dist_eq, Real.dist_eq] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ K.2)
  calc |max 0 (min a 1) - max 0 (min b 1)| ≤ |min a 1 - min b 1| := by
        rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ ≤ |a - b| := by
        have := abs_min_sub_min_le_max a 1 b 1
        simpa using this

theorem sq_diff {ck ch : ℂ} {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (h1 : ‖ck - ch‖ ^ 2 ≤ 4 * δ ^ 2 * a * b) (h2 : ‖ch‖ ^ 2 ≤ a * b) :
    |‖ck‖ ^ 2 - ‖ch‖ ^ 2| ≤ 5 * δ * (a * b) := by
  have hP : 0 ≤ a * b := mul_nonneg ha hb
  have hxe := abs_norm_sub_norm_le ck ch
  have hd := norm_nonneg (ck - ch)
  have he := norm_nonneg ch
  have hx := norm_nonneg ck
  have hde : ‖ck - ch‖ * ‖ch‖ ≤ 2 * δ * (a * b) := by
    by_contra H
    push Not at H
    have h3 := mul_self_lt_mul_self (by positivity) H
    have h4 := mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    nlinarith
  have h5 : 0 ≤ δ * (1 / 4 - δ) * (a * b) := mul_nonneg (mul_nonneg hδ (sub_nonneg.2 hδ1)) hP
  rw [abs_le] at hxe ⊢
  have u1 := mul_le_mul_of_nonneg_right hxe.2 (add_nonneg hx he)
  have u2 := mul_le_mul_of_nonneg_left (show ‖ck‖ ≤ ‖ch‖ + ‖ck - ch‖ by linarith [hxe.2]) hd
  have l1 := mul_le_mul_of_nonneg_right (show ‖ch‖ - ‖ck‖ ≤ ‖ck - ch‖ by linarith [hxe.1]) (add_nonneg he hx)
  constructor <;> nlinarith

theorem alg_bound {s A δ Zh FinalFormK Sh Sk M m C₁ c : ℝ} (hs : 0 < s) (hm : 0 < m) (hZh : m ≤ Zh)
    (hZk : m ≤ FinalFormK) (hM : M ≤ C₁ * m) (hC₁ : 0 ≤ C₁) (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hSh0 : 0 ≤ Sh) (hSh : Sh ≤ 4 * s * A * Zh) (hS : |Sk - Sh| ≤ M * δ * s * A * c)
    (hZ : |FinalFormK - Zh| ≤ M * δ * c) :
    |(s ^ 2 * FinalFormK)⁻¹ * Sk - (s ^ 2 * Zh)⁻¹ * Sh| ≤ C₁ * (5 * c) * δ / s * A := by
  have hZh0 : 0 < Zh := hm.trans_le hZh
  have hZk0 : 0 < FinalFormK := hm.trans_le hZk
  have hs0 : s ≠ 0 := hs.ne'
  have hZh1 : Zh ≠ 0 := hZh0.ne'
  have hZk1 : FinalFormK ≠ 0 := hZk0.ne'
  have e : (s ^ 2 * FinalFormK)⁻¹ * Sk - (s ^ 2 * Zh)⁻¹ * Sh =
      ((Sk - Sh) * Zh + Sh * (Zh - FinalFormK)) / (s ^ 2 * Zh * FinalFormK) := by
    field_simp <;> ring
  have hden : 0 < s ^ 2 * Zh * FinalFormK := mul_pos (mul_pos (pow_pos hs 2) hZh0) hZk0
  rw [e, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have h1 : |(Sk - Sh) * Zh + Sh * (Zh - FinalFormK)| ≤ |Sk - Sh| * Zh + Sh * |Zh - FinalFormK| := by
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_pos hZh0, abs_of_nonneg hSh0]
  have h4 : 0 ≤ 4 * s * A * Zh := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs.le) hA) hZh0.le
  have h2 : |Sk - Sh| * Zh + Sh * |Zh - FinalFormK| ≤
      M * δ * s * A * c * Zh + 4 * s * A * Zh * (M * δ * c) :=
    add_le_add (mul_le_mul_of_nonneg_right hS hZh0.le)
      (mul_le_mul hSh (by rw [abs_sub_comm]; exact hZ) (abs_nonneg _) h4)
  have hMZ : M ≤ C₁ * FinalFormK := hM.trans (mul_le_mul_of_nonneg_left hZk hC₁)
  have hP : 0 ≤ δ * s * A * c * Zh :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hδ hs.le) hA) hc) hZh0.le
  have eR : C₁ * (5 * c) * δ / s * A * (s ^ 2 * Zh * FinalFormK) = 5 * (C₁ * FinalFormK) * (δ * s * A * c * Zh) := by
    field_simp <;> ring
  have eL : M * δ * s * A * c * Zh + 4 * s * A * Zh * (M * δ * c) = 5 * M * (δ * s * A * c * Zh) := by
    ring
  rw [eR]
  refine (h1.trans h2).trans ?_
  rw [eL]
  exact mul_le_mul_of_nonneg_right (by linarith) hP

end PositivityTheory.KB.SmoothPartitionUnityBasic.TraceLipschitz
