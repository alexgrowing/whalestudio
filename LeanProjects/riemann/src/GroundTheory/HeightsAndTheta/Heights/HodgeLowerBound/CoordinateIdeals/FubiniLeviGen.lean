import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi

open ReciprocityTheory.ChartRestriction.G.Geo

variable {J : Type} [Fintype J]

theorem lagrange_sum (z w : J → ℂ) :
    ∑ p, ∑ q, Complex.normSq (z p * w q - z q * w p) =
      2 * (sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2)) := by
  set r : J → ℝ := fun p => (z p).re * (w p).re + (z p).im * (w p).im with hr
  set s : J → ℝ := fun p => (z p).im * (w p).re - (z p).re * (w p).im with hs
  set G : J → J → ℝ := fun p q => ‖z p‖ ^ 2 * ‖w q‖ ^ 2 - r p * r q - s p * s q with hG
  have hrw : reInner z w = ∑ p, r p := by rw [reInner_apply]
  have hsw : reInner z (Complex.I • w) = ∑ p, s p := by
    rw [reInner_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hs]
    ring
  have key : ∀ p q, Complex.normSq (z p * w q - z q * w p) = G p q + G q p := by
    intro p q
    simp only [hG, hr, hs, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im]
    ring
  have hsym : ∑ p, ∑ q, G q p = ∑ p, ∑ q, G p q := Finset.sum_comm
  have hexp : sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2) = ∑ p, ∑ q, G p q := by
    rw [hrw, hsw, sqSum, sqSum, sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hG]
    ring
  simp_rw [key, Finset.sum_add_distrib]
  rw [hsym, hexp]
  ring

theorem sqSum_ne_zero {z : J → ℂ} (hz : ∃ i, z i ≠ 0) : sqSum z ≠ 0 := by
  obtain ⟨i, hi⟩ := hz
  refine ne_of_gt (lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) ?_)
  exact Finset.single_le_sum (f := fun p => ‖z p‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem levi_phi_pos_of_ne {z w : J → ℂ} (hz : ∃ i, z i ≠ 0)
    (hw : ∀ c : ℂ, w ≠ fun p => c * z p) : 0 < leviForm phi z w := by
  have hS := sqSum_ne_zero hz
  rw [leviForm_phi hS]
  have hnum : 0 < sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2) := by
    have h2 := lagrange_sum z w
    have hnn : 0 ≤ ∑ p, ∑ q, Complex.normSq (z p * w q - z q * w p) :=
      Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _
    rcases hnn.lt_or_eq with hlt | heq
    · linarith
    · exfalso
      obtain ⟨i, hi⟩ := hz
      have hall : ∀ p q, Complex.normSq (z p * w q - z q * w p) = 0 := by
        intro p q
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => Finset.sum_nonneg fun q _ =>
          Complex.normSq_nonneg (z p * w q - z q * w p))).1 heq.symm p (Finset.mem_univ _)
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => Complex.normSq_nonneg _)).1 h1 q
          (Finset.mem_univ _)
      apply hw (w i / z i)
      funext q
      have h := hall i q
      rw [Complex.normSq_eq_zero, sub_eq_zero] at h
      rw [div_mul_eq_mul_div, eq_div_iff hi]
      linear_combination h
  exact div_pos (by linarith) (by have := sqSum_nonneg z; positivity)

end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
