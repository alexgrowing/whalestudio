import Mathlib

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

namespace ComplexPowerDifferenceIntegral

lemma cpow_sub_eq_integral' {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {s : ℂ} (hs : s ≠ 0) :
    (x : ℂ) ^ (-s) - (y : ℂ) ^ (-s) = s * ∫ t in x..y, (t : ℂ) ^ (-s - 1) := by
  have h0 : (0:ℝ) ∉ Set.uIcc x y := by
    rw [Set.uIcc_of_le hxy]; intro h; exact absurd h.1 (not_le.mpr hx)
  have hr : (-s - 1) ≠ -1 := by intro h; apply hs; linear_combination -h
  have hs' : -s ≠ 0 := neg_ne_zero.mpr hs
  rw [integral_cpow (Or.inr ⟨hr, h0⟩)]
  have e : -s - 1 + 1 = -s := by ring
  rw [e, mul_div_assoc', eq_div_iff hs']
  ring

lemma norm_cpow_sub_le_point {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxa : x ≤ a + 1) {s : ℂ}
    (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hxpos : 0 < x := lt_of_lt_of_le ha hax
  rw [cpow_sub_eq_integral' hxpos hxa hs0, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hC : ∀ t ∈ Set.uIoc x (a + 1), ‖(t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re - 1) := by
    intro t ht
    rw [Set.uIoc_of_le hxa] at ht
    have hta : a ≤ t := le_trans hax ht.1.le
    have ht0 : 0 < t := lt_of_lt_of_le ha hta
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact Real.rpow_le_rpow_of_nonpos ha hta (by linarith)
  calc ‖∫ t in x..(a + 1), (t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re - 1) * |a + 1 - x| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hC
    _ ≤ a ^ (-s.re - 1) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ha.le _)
        rw [abs_of_nonneg (by linarith)]; linarith
    _ = a ^ (-s.re - 1) := mul_one _

def eint (s : ℂ) (a : ℝ) : ℂ := ∫ x in a..(a + 1), ((x : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s))

lemma norm_eint_le {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    ‖eint s a‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
  unfold eint
  have hC : ∀ x ∈ Set.uIoc a (a + 1),
      ‖((x : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s))‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    exact norm_cpow_sub_le_point ha hx.1.le hx.2 hs
  calc _ ≤ ‖s‖ * a ^ (-s.re - 1) * |a + 1 - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hC
    _ = _ := by rw [show a + 1 - a = 1 by ring, abs_one, mul_one]

lemma d_eq {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (a : ℂ) ^ (1 - s) - ((a + 1 : ℝ) : ℂ) ^ (1 - s) - (s - 1) * ((a + 1 : ℝ) : ℂ) ^ (-s) =
      (s - 1) * eint s a := by
  unfold eint
  by_cases hs1 : s = 1
  · subst hs1; simp
  have h0 : (0:ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]; intro h; linarith [h.1]
  have hr : -s ≠ -1 := by intro h; apply hs1; linear_combination -h
  have hint1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume a (a + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr h0)
  rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const,
    integral_cpow (Or.inr ⟨hr, h0⟩), intervalIntegral.integral_const]
  have e : -s + 1 = 1 - s := by ring
  rw [e]
  have hs' : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [Complex.real_smul]
  push_cast
  field_simp
  ring

end ComplexPowerDifferenceIntegral

end Formalism.ZF
