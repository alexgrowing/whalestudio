import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.SecondDiff

lemma half_le_norm {z w : ℂ} (hw : ‖w - z‖ ≤ ‖z‖ / 2) : ‖z‖ / 2 ≤ ‖w‖ := by
  have h := norm_sub_norm_le z w
  rw [norm_sub_rev] at h
  linarith

lemma ne_zero_of_near {z w : ℂ} (hz : z ≠ 0) (hw : ‖w - z‖ ≤ ‖z‖ / 2) : w ≠ 0 := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h := half_le_norm hw
  intro h0
  rw [h0, norm_zero] at h
  linarith

lemma zpow_neg_lip (n : ℕ) {z u v : ℂ} (hz : z ≠ 0)
    (hu : ‖u - z‖ ≤ ‖z‖ / 2) (hv : ‖v - z‖ ≤ ‖z‖ / 2) :
    ‖u ^ (-(n:ℤ)) - v ^ (-(n:ℤ))‖ ≤ n * (2 / ‖z‖) ^ (n + 1) * ‖u - v‖ := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hmem : ∀ w ∈ Metric.closedBall z (‖z‖ / 2), ‖w - z‖ ≤ ‖z‖ / 2 := by
    intro w hw; simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hd : ∀ w ∈ Metric.closedBall z (‖z‖ / 2), HasDerivAt (fun x : ℂ => x ^ (-(n:ℤ)))
      (((-(n:ℤ) : ℤ) : ℂ) * w ^ (-(n:ℤ) - 1)) w :=
    fun w hw => hasDerivAt_zpow _ w (Or.inl (ne_zero_of_near hz (hmem w hw)))
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x : ℂ => x ^ (-(n:ℤ)))
    (s := Metric.closedBall z (‖z‖ / 2)) (x := v) (y := u) (C := n * (2 / ‖z‖) ^ (n + 1))
    (fun w hw => (hd w hw).differentiableAt)
    (fun w hw => by
      rw [(hd w hw).deriv]
      have hw' : ‖z‖ / 2 ≤ ‖w‖ := half_le_norm (hmem w hw)
      have hwpos : 0 < ‖w‖ := by linarith
      rw [norm_mul, norm_zpow]
      have e1 : ‖(((-(n:ℤ)) : ℤ) : ℂ)‖ = n := by simp
      have e2 : -(n:ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2, zpow_neg, zpow_natCast, ← inv_div, inv_pow]
      gcongr)
    (convex_closedBall z _)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hv)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hu)
  simpa using key

theorem second_diff_inv_pow : ∀ j : ℕ, ∃ C : ℝ, ∀ z a b : ℂ, z ≠ 0 → 4 * ‖a‖ ≤ ‖z‖ → 4 * ‖b‖ ≤ ‖z‖ →
    ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹‖
      ≤ C * ‖a‖ * ‖b‖ / ‖z‖ ^ (j + 2) := by
  intro j
  refine ⟨j * (j + 1) * 2 ^ (j + 2), ?_⟩
  intro z a b hz ha hb
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set g : ℂ → ℂ := fun w => w ^ (-(j:ℤ)) - (w + a) ^ (-(j:ℤ)) with hg
  have hmem : ∀ w ∈ Metric.closedBall z (‖z‖ / 4), ‖w - z‖ ≤ ‖z‖ / 2 ∧ ‖w + a - z‖ ≤ ‖z‖ / 2 := by
    intro w hw
    have h : ‖w - z‖ ≤ ‖z‖ / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    refine ⟨by linarith, ?_⟩
    calc ‖w + a - z‖ = ‖(w - z) + a‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖a‖ := norm_add_le _ _
      _ ≤ ‖z‖ / 2 := by linarith
  have hd : ∀ w ∈ Metric.closedBall z (‖z‖ / 4), HasDerivAt g
      ((((-(j:ℤ)) : ℤ) : ℂ) * (w ^ (-(j:ℤ) - 1) - (w + a) ^ (-(j:ℤ) - 1))) w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hmem w hw
    have d1 := hasDerivAt_zpow (-(j:ℤ)) w (Or.inl (ne_zero_of_near hz h1))
    have d2 := (hasDerivAt_zpow (-(j:ℤ)) (w + a) (Or.inl (ne_zero_of_near hz h2))).comp_add_const w a
    rw [mul_sub]
    exact d1.sub d2
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := g)
    (s := Metric.closedBall z (‖z‖ / 4)) (x := z) (y := z + b)
    (C := j * ((j + 1 : ℕ) * (2 / ‖z‖) ^ ((j + 1 : ℕ) + 1) * ‖a‖))
    (fun w hw => (hd w hw).differentiableAt)
    (fun w hw => by
      rw [(hd w hw).deriv, norm_mul]
      obtain ⟨h1, h2⟩ := hmem w hw
      have e1 : ‖(((-(j:ℤ)) : ℤ) : ℂ)‖ = j := by simp
      have e2 : -(j:ℤ) - 1 = -((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2]
      have L := zpow_neg_lip (j + 1) hz h1 h2
      have e3 : ‖w - (w + a)‖ = ‖a‖ := by rw [sub_add_cancel_left, norm_neg]
      rw [e3] at L
      gcongr)
    (convex_closedBall z _)
    (by simp [Metric.mem_closedBall, dist_eq_norm]; positivity)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using (by linarith : ‖b‖ ≤ ‖z‖ / 4))
  have eq : (z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹ = -(g (z + b) - g z) := by
    simp only [hg, zpow_neg, zpow_natCast]
    rw [show z + b + a = z + a + b by ring]
    ring
  rw [eq, norm_neg]
  refine key.trans (le_of_eq ?_)
  rw [add_sub_cancel_left, div_pow]
  push_cast
  field_simp

end GlobalTheory.EisM.SecondDiff
