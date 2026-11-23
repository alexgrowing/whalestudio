import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StEntirePolynomialGrowth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Metric

theorem entire_polynomialGrowth_one_var (M : ℕ) : ∀ (g : ℂ → ℂ) (C : ℝ), Differentiable ℂ g →
    (∀ z, ‖g z‖ ≤ C * (1 + ‖z‖) ^ M) →
    ∃ q : Polynomial ℂ, q.natDegree ≤ M ∧ ∀ z, g z = q.eval z := by
  induction M with
  | zero =>
    intro g C hg hb
    refine ⟨Polynomial.C (g 0), by simp, fun z => ?_⟩
    rw [Polynomial.eval_C]
    refine hg.apply_eq_apply_of_bounded ?_ z 0
    refine isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩
    rintro _ ⟨w, rfl⟩
    simpa using hb w
  | succ M ih =>
    intro g C hg hb
    set h := dslope g 0 with hh
    have hdiff : Differentiable ℂ h := by
      rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hg.differentiableOn
    obtain ⟨B, hB⟩ : ∃ B, ∀ z ∈ closedBall (0 : ℂ) 1, ‖h z‖ ≤ B :=
      (isCompact_closedBall 0 1).exists_bound_of_continuousOn hdiff.continuous.continuousOn
    have hrep : ∀ z, g z = g 0 + z * h z := fun z => by
      have := sub_smul_dslope g 0 z
      rw [smul_eq_mul, sub_zero] at this
      linear_combination -this
    set C' := max C 0 with hC'def
    have hC' : 0 ≤ C' := le_max_right _ _
    have hb' : ∀ z, ‖g z‖ ≤ C' * (1 + ‖z‖) ^ (M + 1) := fun z =>
      (hb z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hgrowth : ∀ z, ‖h z‖ ≤ (max B 0 + 2 * C' + ‖g 0‖) * (1 + ‖z‖) ^ M := by
      intro z
      have hg0 := norm_nonneg (g 0)
      have hBm := le_max_left B 0
      have hB0 := le_max_right B 0
      rcases le_or_gt ‖z‖ 1 with hz | hz
      · have h1 : 1 ≤ (1 + ‖z‖) ^ M := one_le_pow₀ (by linarith [norm_nonneg z])
        have := hB z (by simpa using hz)
        nlinarith
      · have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
        have hhz : h z = (g z - g 0) / z := by
          rw [hh, dslope_of_ne _ hz0, slope_def_field, sub_zero]
        rw [hhz, norm_div, div_le_iff₀ (by positivity)]
        have e1 := norm_sub_le (g z) (g 0)
        have e2 := hb' z
        have hP : 1 ≤ (1 + ‖z‖) ^ M := one_le_pow₀ (by linarith [norm_nonneg z])
        have hs : (1 + ‖z‖) ^ (M + 1) = (1 + ‖z‖) ^ M * (1 + ‖z‖) := pow_succ _ _
        rw [hs] at e2
        have k1 : 0 ≤ C' * (1 + ‖z‖) ^ M * (‖z‖ - 1) :=
          mul_nonneg (mul_nonneg hC' (by positivity)) (by linarith)
        have k2 : 0 ≤ ‖g 0‖ * ((1 + ‖z‖) ^ M * ‖z‖ - 1) :=
          mul_nonneg hg0 (by nlinarith)
        have k3 : 0 ≤ max B 0 * (1 + ‖z‖) ^ M * ‖z‖ := by positivity
        nlinarith
    obtain ⟨q, hqdeg, hq⟩ := ih h (max B 0 + 2 * C' + ‖g 0‖) hdiff hgrowth
    refine ⟨Polynomial.C (g 0) + Polynomial.X * q, ?_, fun z => ?_⟩
    · calc (Polynomial.C (g 0) + Polynomial.X * q).natDegree
          ≤ max (Polynomial.C (g 0)).natDegree (Polynomial.X * q).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ M + 1 := by
            refine max_le (by simp) (Polynomial.natDegree_mul_le.trans ?_)
            have := Polynomial.natDegree_X_le (R := ℂ)
            omega
    · rw [hrep z, hq z]; simp

theorem EntirePolynomialGrowth.proof : EntirePolynomialGrowth.Statement := by
  intro d
  induction d with
  | zero =>
    intro f C M _ _
    refine ⟨MvPolynomial.C (f 0), fun y => ?_⟩
    rw [MvPolynomial.eval_C]
    congr 1
    exact Subsingleton.elim _ _
  | succ d ih =>
    intro f C M hf hb
    set C' := max C 0 with hC'def
    have hC' : 0 ≤ C' := le_max_right _ _
    have hb' : ∀ y, ‖f y‖ ≤ C' * (1 + ‖y‖) ^ M := fun y =>
      (hb y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hcons : ∀ (c : ℂ) (w : Fin d → ℂ), ‖(Fin.cons c w : Fin (d + 1) → ℂ)‖ ≤ ‖c‖ + ‖w‖ := by
      intro c w
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [norm_nonneg]
      · simp only [Fin.cons_succ]
        linarith [norm_le_pi_norm w i, norm_nonneg c]
    have hdc : ∀ w : Fin d → ℂ, Differentiable ℂ (fun z : ℂ => (Fin.cons z w : Fin (d + 1) → ℂ)) := by
      intro w
      refine differentiable_pi.2 fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; fun_prop
      · simp only [Fin.cons_succ]; fun_prop
    have hdw : ∀ c : ℂ, Differentiable ℂ (fun w : Fin d → ℂ => (Fin.cons c w : Fin (d + 1) → ℂ)) := by
      intro c
      refine differentiable_pi.2 fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; fun_prop
      · simp only [Fin.cons_succ]; fun_prop
    have hp : ∀ j : ℕ, ∃ p : MvPolynomial (Fin d) ℂ,
        ∀ w, f (Fin.cons (j : ℂ) w) = eval w p := by
      intro j
      refine ih _ (C' * (1 + (j : ℝ)) ^ M) M (hf.comp (hdw _)) fun w => ?_
      have hn := hcons (j : ℂ) w
      rw [Complex.norm_natCast] at hn
      calc ‖f (Fin.cons (j : ℂ) w)‖
          ≤ C' * (1 + ‖(Fin.cons (j : ℂ) w : Fin (d + 1) → ℂ)‖) ^ M := hb' _
        _ ≤ C' * ((1 + (j : ℝ)) * (1 + ‖w‖)) ^ M := by
            gcongr
            nlinarith [norm_nonneg w, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        _ = C' * (1 + (j : ℝ)) ^ M * (1 + ‖w‖) ^ M := by rw [mul_pow, mul_assoc]
    choose p hp using hp
    have hz : ∀ w : Fin d → ℂ, ∃ q : Polynomial ℂ, q.natDegree ≤ M ∧
        ∀ z, f (Fin.cons z w) = q.eval z := by
      intro w
      refine entire_polynomialGrowth_one_var M _ (C' * (1 + ‖w‖) ^ M) (hf.comp (hdc w)) fun z => ?_
      have hn := hcons z w
      calc ‖f (Fin.cons z w)‖ ≤ C' * (1 + ‖(Fin.cons z w : Fin (d + 1) → ℂ)‖) ^ M := hb' _
        _ ≤ C' * ((1 + ‖w‖) * (1 + ‖z‖)) ^ M := by
            gcongr
            nlinarith [norm_nonneg w, norm_nonneg z]
        _ = C' * (1 + ‖w‖) ^ M * (1 + ‖z‖) ^ M := by rw [mul_pow, mul_assoc]
    refine ⟨∑ j ∈ Finset.range (M + 1),
      Polynomial.aeval (X 0 : MvPolynomial (Fin (d + 1)) ℂ)
        (Lagrange.basis (Finset.range (M + 1)) (fun j : ℕ => (j : ℂ)) j) * rename Fin.succ (p j),
      fun y => ?_⟩
    obtain ⟨q, hqd, hq⟩ := hz (Fin.tail y)
    have hinj : Set.InjOn (fun j : ℕ => (j : ℂ)) (Finset.range (M + 1) : Set ℕ) :=
      Nat.cast_injective.injOn
    have hdeg : q.degree < (Finset.range (M + 1)).card := by
      rw [Finset.card_range]
      exact (Polynomial.degree_le_of_natDegree_le hqd).trans_lt (by exact_mod_cast Nat.lt_succ_self M)
    have key := Lagrange.eq_interpolate hinj hdeg
    have hev : ∀ P : Polynomial ℂ,
        eval y (Polynomial.aeval (X 0 : MvPolynomial (Fin (d + 1)) ℂ) P) = P.eval (y 0) := by
      intro P
      have hid : (eval y).comp (algebraMap ℂ (MvPolynomial (Fin (d + 1)) ℂ)) = RingHom.id ℂ := by
        ext; simp
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, MvPolynomial.eval_X, hid]
      rfl
    conv_lhs => rw [← Fin.cons_self_tail y, hq (y 0), key]
    rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hev, eval_rename, Polynomial.eval_mul, Polynomial.eval_C, ← hq, hp, mul_comm]
    rfl

end GroundTheory.Heights₂.Heights.HilbertSamuel
