import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.KroneckerSplitStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

lemma kroneckerTerm_eq (τ : ℍ) {s : ℝ} (hs : 0 < s) (p : ℤ × ℤ) :
    (if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)) =
      τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s) := by
  split_ifs with h
  · subst h
    simp [Real.zero_rpow (mul_pos two_pos hs).ne']
  · rfl

lemma summable_kroneckerTerm (τ : ℍ) {s : ℝ} (hs : 1 < s) :
    Summable fun p : ℤ × ℤ ↦ τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s) := by
  have hk : 2 < 2 * s := by linarith
  have hy : 0 ≤ τ.im ^ s := Real.rpow_nonneg τ.im_pos.le _
  have h1 := (EisensteinSeries.summable_one_div_norm_rpow hk).mul_left
    (τ.im ^ s * EisensteinSeries.r τ ^ (-(2 * s)))
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at h1
  refine Summable.of_nonneg_of_le
    (fun p ↦ div_nonneg hy (Real.rpow_nonneg (norm_nonneg _) _)) (fun p ↦ ?_) h1
  have hb := EisensteinSeries.summand_bound τ (by linarith : (0 : ℝ) ≤ 2 * s)
    ((finTwoArrowEquiv ℤ).symm p)
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.comp_apply] at hb ⊢
  rw [div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg _), mul_assoc]
  exact mul_le_mul_of_nonneg_left hb hy

lemma kroneckerTerm_eq_rpow (τ : ℍ) (s : ℝ) (m n : ℤ) :
    τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) =
      τ.im ^ s * (((n : ℝ) + m * τ.re) ^ 2 + (m * τ.im) ^ 2) ^ (-s) := by
  have h : ‖(m : ℂ) * τ + n‖ ^ 2 = ((n : ℝ) + m * τ.re) ^ 2 + (m * τ.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two, h, Real.rpow_neg (by positivity),
    div_eq_mul_inv]

lemma kroneckerTerm_neg (τ : ℍ) (s : ℝ) (m n : ℤ) :
    τ.im ^ s / ‖((-m : ℤ) : ℂ) * τ + ((-n : ℤ) : ℂ)‖ ^ (2 * s) =
      τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) := by
  rw [show ((-m : ℤ) : ℂ) * τ + ((-n : ℤ) : ℂ) = -((m : ℂ) * τ + n) by push_cast; ring, norm_neg]

lemma tsum_int_split {f : ℤ → ℝ} (h : Summable f) :
    ∑' n : ℤ, f n = ∑' n : ℕ, f (n + 1) + f 0 + ∑' n : ℕ, f (-(n + 1)) :=
  tsum_of_add_one_of_neg_add_one
    (h.comp_injective (show Function.Injective fun n : ℕ ↦ (n : ℤ) + 1 from
      fun a b h ↦ by simpa using h))
    (h.comp_injective (show Function.Injective fun n : ℕ ↦ -((n : ℤ) + 1) from
      fun a b h ↦ by simpa using h))

lemma kroneckerRow_zero (τ : ℍ) {s : ℝ} (hs : 0 < s)
    (h : Summable fun n : ℤ ↦ τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + n‖ ^ (2 * s)) :
    ∑' n : ℤ, τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + n‖ ^ (2 * s) =
      2 * τ.im ^ s * ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ (2 * s)) := by
  rw [tsum_int_split h]
  have e1 : ∀ n : ℕ, τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + (((n : ℤ) + 1 : ℤ) : ℂ)‖ ^ (2 * s) =
      τ.im ^ s * (1 / ((n + 1 : ℝ) ^ (2 * s))) := by
    intro n
    have : ‖((0 : ℤ) : ℂ) * τ + (((n : ℤ) + 1 : ℤ) : ℂ)‖ = (n : ℝ) + 1 := by
      rw [show ((0 : ℤ) : ℂ) * τ + (((n : ℤ) + 1 : ℤ) : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [this, mul_one_div]
  have e2 : ∀ n : ℕ, τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + ((-((n : ℤ) + 1) : ℤ) : ℂ)‖ ^ (2 * s) =
      τ.im ^ s * (1 / ((n + 1 : ℝ) ^ (2 * s))) := by
    intro n
    rw [← e1 n]
    simpa using kroneckerTerm_neg τ s 0 ((n : ℤ) + 1)
  have e0 : τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + ((0 : ℤ) : ℂ)‖ ^ (2 * s) = 0 := by
    simp [Real.zero_rpow (mul_pos two_pos hs).ne']
  simp only [e1, e2, e0, add_zero, tsum_mul_left]
  ring

lemma kroneckerRow_neg (τ : ℍ) (s : ℝ) (m : ℤ) :
    ∑' n : ℤ, τ.im ^ s / ‖((-m : ℤ) : ℂ) * τ + n‖ ^ (2 * s) =
      ∑' n : ℤ, τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) := by
  rw [← tsum_comp_neg]
  exact tsum_congr fun n ↦ kroneckerTerm_neg τ s m n

theorem KroneckerSplit.proof : KroneckerSplit.Statement := by
  intro τ s hs
  have hs0 : 0 < s := by linarith
  have hsum := summable_kroneckerTerm τ hs
  have hcol : Summable fun m : ℤ ↦ ∑' n : ℤ, τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) :=
    hsum.prod
  rw [kroneckerSum, tsum_congr (kroneckerTerm_eq τ hs0), hsum.tsum_prod, tsum_int_split hcol]
  have hrow0 : Summable fun n : ℤ ↦ τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + n‖ ^ (2 * s) :=
    hsum.prod_factor 0
  simp only [kroneckerRow_neg, kroneckerRow_zero τ hs0 hrow0]
  have e : ∀ m : ℕ, ∑' n : ℤ, τ.im ^ s / ‖(((m : ℤ) + 1 : ℤ) : ℂ) * τ + n‖ ^ (2 * s) =
      τ.im ^ s * ∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s) := by
    intro m
    rw [← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [kroneckerTerm_eq_rpow]
    push_cast
    rfl
  simp only [e]
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
