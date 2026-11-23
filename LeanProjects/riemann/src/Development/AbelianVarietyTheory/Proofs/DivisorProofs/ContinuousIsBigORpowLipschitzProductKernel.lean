import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Formalism.LatticeTheta.Statement

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

theorem mul_im_pos_of_sign_mul_pos {w : ℂ} {t : ℝ} (h : 0 < (SignType.sign w.im : ℝ) * t) :
    0 < t * w.im := by
  rcases lt_trichotomy w.im 0 with hw | hw | hw
  · rw [sign_neg hw] at h
    simp at h
    nlinarith
  · rw [hw, sign_zero] at h
    simp at h
  · rw [sign_pos hw] at h
    simp at h
    positivity

theorem norm_lipschitzOneVariableKernel_le (k : ℕ) (w : ℂ) (t : ℝ) :
    ‖phi1 k w t‖ ≤ |t| ^ (k - 1) * Real.exp (-(2 * Real.pi * |w.im|) * |t|) := by
  unfold phi1
  split_ifs with h
  · have hp := mul_im_pos_of_sign_mul_pos h
    have habs : |t| * |w.im| = t * w.im := by rw [← abs_mul]; exact abs_of_pos hp
    have hre : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * w).re = -(2 * Real.pi * |w.im|) * |t| := by
      simp [Complex.mul_re]
      linear_combination (-2 * Real.pi) * habs
    rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  · simp only [norm_zero]
    positivity

theorem abs_pow_mul_exp_le (n : ℕ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |t| ^ n * Real.exp (-a * |t|) ≤ (n.factorial * (2 / a) ^ n) * Real.exp (-(a / 2) * |t|) := by
  have h := Real.pow_div_factorial_le_exp (a / 2 * |t|) (by positivity) n
  rw [div_le_iff₀ (by positivity)] at h
  have h1 : |t| ^ n ≤ n.factorial * (2 / a) ^ n * Real.exp (a / 2 * |t|) := by
    calc |t| ^ n = (2 / a) ^ n * (a / 2 * |t|) ^ n := by
          rw [← mul_pow]; congr 1; field_simp
      _ ≤ (2 / a) ^ n * (Real.exp (a / 2 * |t|) * n.factorial) := by gcongr
      _ = _ := by ring
  calc |t| ^ n * Real.exp (-a * |t|)
      ≤ (n.factorial * (2 / a) ^ n * Real.exp (a / 2 * |t|)) * Real.exp (-a * |t|) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem continuous_lipschitzOneVariableKernel {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w.im ≠ 0) : Continuous (phi1 k w) := by
  have hg : Continuous fun t : ℝ =>
      ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w) := by fun_prop
  show Continuous fun t => if 0 < (SignType.sign w.im : ℝ) * t then
    ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w) else 0
  refine continuous_if (fun a ha => ?_) hg.continuousOn continuous_const.continuousOn
  have h0 := frontier_lt_subset_eq (continuous_const (y := (0 : ℝ)))
    (continuous_const.mul continuous_id (f := fun _ : ℝ => (SignType.sign w.im : ℝ))) ha
  simp only [Set.mem_setOf_eq, id] at h0
  have ha0 : a = 0 := by
    rcases mul_eq_zero.1 h0.symm with h | h
    · exfalso
      rcases lt_trichotomy w.im 0 with h' | h' | h'
      · rw [sign_neg h'] at h; norm_num at h
      · exact hw h'
      · rw [sign_pos h'] at h; norm_num at h
    · exact h
  subst ha0
  have : k - 1 ≠ 0 := by omega
  simp [this]

end GlobalTheory.LipschitzTR

namespace GlobalTheory.LipschitzTR

theorem norm_le_sum_abs {F : Type} [Field F] [NumberField F] (v : RSp F) :
    ‖v‖ ≤ ∑ τ, |v τ| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simpa [Real.norm_eq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun τ => |v τ|) fun _ _ => abs_nonneg _

theorem continuous_and_isBigO_rpow_Phi (F : Type) [Field F] [NumberField F] (k : ℕ) (hk : 2 ≤ k)
    (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Continuous (Phi k z) ∧ ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := by
  refine ⟨?_, fun b => ?_⟩
  · unfold Phi
    exact continuous_finset_prod _ fun τ _ =>
      (continuous_lipschitzOneVariableKernel hk (hz τ)).comp ((EuclideanSpace.proj τ : RSp F →L[ℝ] ℝ).continuous)
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ τ, c ≤ 2 * Real.pi * |(z τ).im| / 2 := by
    rcases isEmpty_or_nonempty (F →+* ℝ) with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · obtain ⟨τ0, hτ0⟩ := Finite.exists_min (fun τ => 2 * Real.pi * |(z τ).im| / 2)
      exact ⟨_, by have := abs_pos.2 (hz τ0); positivity, hτ0⟩
  set K : ℝ := ∏ τ, (((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) with hK
  have hbound : ∀ v : RSp F, ‖Phi k z v‖ ≤ K * Real.exp (-c * ‖v‖) := by
    intro v
    have hfac : ∀ τ, ‖phi1 k (z τ) (v τ)‖ ≤
        (((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) *
          Real.exp (-c * |v τ|) := by
      intro τ
      have ha : 0 < 2 * Real.pi * |(z τ).im| := by have := abs_pos.2 (hz τ); positivity
      refine (norm_lipschitzOneVariableKernel_le k (z τ) (v τ)).trans ((abs_pow_mul_exp_le (k - 1) ha (v τ)).trans ?_)
      gcongr
      have := hcle τ
      nlinarith [abs_nonneg (v τ)]
    calc ‖Phi k z v‖ = ∏ τ, ‖phi1 k (z τ) (v τ)‖ := by unfold Phi; rw [norm_prod]
      _ ≤ ∏ τ, ((((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) *
          Real.exp (-c * |v τ|)) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => hfac τ
      _ = K * Real.exp (-c * ∑ τ, |v τ|) := by
        rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
      _ ≤ K * Real.exp (-c * ‖v‖) := by
        have hK0 : 0 ≤ K := Finset.prod_nonneg fun τ _ => by positivity
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [norm_le_sum_abs v])) hK0
  have h1 : Phi k z =O[Filter.cocompact (RSp F)] fun v : RSp F => Real.exp (-c * ‖v‖) :=
    Asymptotics.IsBigO.of_bound K (Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hbound v)
  have h2 : (fun v : RSp F => Real.exp (-c * ‖v‖)) =O[Filter.cocompact (RSp F)]
      fun v : RSp F => ‖v‖ ^ (-b) :=
    (isLittleO_exp_neg_mul_rpow_atTop hc (-b)).isBigO.comp_tendsto tendsto_norm_cocompact_atTop
  exact h1.trans h2

end GlobalTheory.LipschitzTR
