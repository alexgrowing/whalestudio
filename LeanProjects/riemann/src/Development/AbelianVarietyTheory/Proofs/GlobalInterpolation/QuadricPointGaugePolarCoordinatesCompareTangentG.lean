import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.PolarCompare

theorem abs_sqrt_sub_one_le (x : ℝ) : |Real.sqrt (1 - x) - 1| ≤ |x| := by
  rcases le_or_gt (1 - x) 0 with h | h
  · rw [Real.sqrt_eq_zero_of_nonpos h]
    have : |(0:ℝ) - 1| = 1 := by norm_num
    rw [this]
    exact le_trans (by linarith) (le_abs_self x)
  · have h1 := Real.sq_sqrt h.le
    have h2 := Real.sqrt_nonneg (1 - x)
    set a := Real.sqrt (1 - x)
    have h3 : x = (1 - a) * (1 + a) := by linarith
    rw [h3, abs_mul, abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ 1 + a)]
    have := abs_nonneg (1 - a)
    nlinarith

theorem abs_qf_le {P Q : ℕ} (z : Sp P Q) : |qf z| ≤ (∑ i, ‖z i‖) ^ 2 := by
  rw [qf_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (le_of_eq ?_) (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg (z i)))
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_mul, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖z i‖)]
  rcases sg_eq i with h | h <;> simp [h]

theorem norm_exp_eq (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one]
  simp

theorem abs_sin_eq (x : ℝ) (h : |x| ≤ Real.pi) : |Real.sin x| = Real.sin |x| := by
  rcases le_total 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 h)
  · rw [abs_of_nonpos h0] at h ⊢
    rw [← abs_neg, ← Real.sin_neg]
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h)

theorem exp_bounds (θ : ℝ) (h : |θ| ≤ Real.pi) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ |θ| ∧
    |θ| ≤ 2 * ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ∧
    (|θ| ≤ 2 → |θ| - |θ| ^ 3 / 16 ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖) := by
  have hp := Real.pi_pos
  have h0 := abs_nonneg θ
  have e1 : |θ / 2| = |θ| / 2 := by rw [abs_div]; norm_num
  rw [norm_exp_eq, abs_sin_eq _ (by rw [e1]; linarith), e1]
  set T := |θ|
  refine ⟨?_, ?_, fun h2 => ?_⟩
  · have := Real.sin_le (x := T / 2) (by linarith)
    linarith
  · have h1 := Real.mul_le_sin (x := T / 2) (by linarith) (by linarith)
    have h2 : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
      rw [div_le_div_iff₀ (by norm_num) hp]
      have := Real.pi_le_four
      linarith
    nlinarith
  · rcases h0.eq_or_lt with h3 | h3
    · rw [← h3]; simp
    · have := Real.sin_gt_sub_cube (x := T / 2) (by linarith)
      nlinarith [pow_nonneg h0 3]

theorem polar_compare (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ)
    (ht : 1 < t) : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q',
      u.1 ∈ Set.Ioo (-Real.pi) Real.pi →
      (tanGauge u < t⁻¹ * r → ptGauge e (polarPt e u) < r) ∧
      (ptGauge e (polarPt e u) < r → tanGauge u < t * r) := by
  have hti : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  have hti0 : 0 < t⁻¹ := inv_pos.2 (by linarith)
  have hd : (0 : ℝ) < min (1 / 2) (min ((t - 1) / 3) (1 - t⁻¹)) := by
    refine lt_min (by norm_num) (lt_min ?_ ?_) <;> linarith
  filter_upwards [Ioo_mem_nhdsGT hd] with r hr u hu
  obtain ⟨hr0, hr1⟩ := hr
  rw [lt_min_iff, lt_min_iff] at hr1
  obtain ⟨hr1, hr2, hr3⟩ := hr1
  obtain ⟨b1, b2, b3⟩ := exp_bounds u.1 (abs_le.2 ⟨hu.1.le, hu.2.le⟩)
  have hq := abs_qf_le u.2
  have ha : |Real.sqrt (1 - sg (e none) * qf u.2) - 1| ≤ (∑ i, ‖u.2 i‖) ^ 2 := by
    refine (abs_sqrt_sub_one_le _).trans (le_trans (le_of_eq ?_) hq)
    rw [abs_mul]
    rcases sg_eq (e none) with h | h <;> simp [h]
  have hN : |‖polarPt e u (e none) - 1‖ - ‖Complex.exp ((u.1 : ℂ) * Complex.I) - 1‖|
      ≤ (∑ i, ‖u.2 i‖) ^ 2 := by
    refine (abs_norm_sub_norm_le _ _).trans (le_trans (le_of_eq ?_) ha)
    rw [polarPt_none]
    set a := Real.sqrt (1 - sg (e none) * qf u.2)
    have : (a : ℂ) * Complex.exp ((u.1 : ℂ) * Complex.I) - 1 -
        (Complex.exp ((u.1 : ℂ) * Complex.I) - 1) =
        ((a - 1 : ℝ) : ℂ) * Complex.exp ((u.1 : ℂ) * Complex.I) := by
      push_cast; ring
    rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have hS : 0 ≤ ∑ i, ‖u.2 i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hN0 := norm_nonneg (polarPt e u (e none) - 1)
  have hT := abs_nonneg u.1
  unfold tanGauge ptGauge
  simp only [polarPt_some]
  obtain ⟨n1, n2⟩ := abs_le.1 hN
  generalize ‖polarPt e u (e none) - 1‖ = N at *
  generalize ‖Complex.exp ((u.1 : ℂ) * Complex.I) - 1‖ = E at *
  generalize ∑ i, ‖u.2 i‖ = S at *
  generalize |u.1| = T at *
  constructor
  · intro h
    have h1 : t⁻¹ * r < r := by nlinarith
    have h2 : S ≤ r := by linarith
    have h3 : S ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hS h2 2
    nlinarith
  · intro h
    have h2 : S ≤ r := by linarith
    have h3 : S ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hS h2 2
    have h4 : r ^ 2 ≤ r := by nlinarith
    have h5 : T ≤ 4 * r := by linarith
    have h6 := b3 (by linarith)
    have h7 : T ^ 3 ≤ (4 * r) ^ 3 := pow_le_pow_left₀ hT h5 3
    have h8 : r ^ 3 ≤ r ^ 2 / 2 := by nlinarith [sq_nonneg r]
    have h9 : 3 * r ^ 2 ≤ (t - 1) * r := by nlinarith
    nlinarith

end GlobalTheory.PolarCompare
