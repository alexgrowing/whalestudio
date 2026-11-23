import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped InnerProductSpace ComplexConjugate

theorem LineQuotientDeterminant.proof : LineQuotientDeterminant.Statement := by
  intro E _ _ _ S hS e he he0 f
  have hne : (0 : ℝ) < ‖e‖ := norm_pos_iff.mpr he0

  have hdet : (Matrix.gram ℂ ![e, f]).det.re = ‖e‖ ^ 2 * ‖f‖ ^ 2 - ‖⟪e, f⟫_ℂ‖ ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← inner_conj_symm e f, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      mul_comm (conj _), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp [Complex.sub_re, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    exact norm_inner_symm f e

  have hee : ⟪e, e⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr he0
  set c : ℂ := ⟪e, f⟫_ℂ / ⟪e, e⟫_ℂ with hc
  set h : E := f - c • e with hh
  have hce : c * ⟪e, e⟫_ℂ = ⟪e, f⟫_ℂ := by
    rw [hc]
    field_simp
  have horth : ⟪e, h⟫_ℂ = 0 := by
    rw [hh, inner_sub_right, inner_smul_right, hce, sub_self]
  have hpyth : ∀ d : ℂ, ‖h + d • e‖ ^ 2 = ‖h‖ ^ 2 + ‖d • e‖ ^ 2 := by
    intro d
    have h0 : ⟪h, d • e⟫_ℂ = 0 := by
      rw [inner_smul_right, inner_eq_zero_symm.mp horth, mul_zero]
    simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) h (d • e) h0
  have hf : f = h + c • e := by rw [hh, sub_add_cancel]
  have hnc : ‖c‖ * ‖e‖ ^ 2 = ‖⟪e, f⟫_ℂ‖ := by
    rw [← hce, norm_mul, inner_self_eq_norm_sq_to_K]
    simp
  have hdet' : (Matrix.gram ℂ ![e, f]).det.re = (‖e‖ * ‖h‖) ^ 2 := by
    have hf2 : ‖f‖ ^ 2 = ‖h‖ ^ 2 + (‖c‖ * ‖e‖) ^ 2 := by
      rw [hf, hpyth c, norm_smul]
    rw [hdet, hf2, ← hnc]
    ring

  have hspan : ∀ s ∈ S, ∃ d : ℂ, d • e = s := by
    intro s hs
    obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, he⟩ : S)
      (by simpa using he0)).mp hS ⟨s, hs⟩
    exact ⟨d, by simpa using congrArg Subtype.val hd⟩

  have hmk : (Submodule.Quotient.mk h : E ⧸ S) = Submodule.Quotient.mk f := by
    rw [Submodule.Quotient.eq, hh, sub_sub_cancel_left]
    exact S.neg_mem (S.smul_mem c he)
  have hq : ‖(Submodule.Quotient.mk f : E ⧸ S)‖ = ‖h‖ := by
    apply le_antisymm
    · rw [← hmk]
      exact Submodule.Quotient.norm_mk_le S h
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨m, hm, hmε⟩ := Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk f : E ⧸ S) hε
      rw [← hmk, Submodule.Quotient.eq] at hm
      obtain ⟨d, hd⟩ := hspan _ hm
      have hm' : m = h + d • e := by rw [hd, add_sub_cancel]
      have : ‖h‖ ^ 2 ≤ ‖m‖ ^ 2 := by
        rw [hm', hpyth d]
        nlinarith [sq_nonneg ‖d • e‖]
      have : ‖h‖ ≤ ‖m‖ := by
        nlinarith [norm_nonneg h, norm_nonneg m]
      linarith
  rw [hdet', hq, Real.sqrt_sq (by positivity)]

end GroundTheory.Heights₂.Heights.FlagBundles
