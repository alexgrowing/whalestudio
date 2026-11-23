import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

theorem exists_shell_of_le_one {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    ∃ j : ℕ, Real.exp (-(j + 1 : ℝ)) < t ∧ t ≤ Real.exp (-(j : ℝ)) := by
  have hl : 0 ≤ -Real.log t := by
    have := Real.log_nonpos h0.le h1
    linarith
  refine ⟨⌊-Real.log t⌋₊, ?_, ?_⟩
  · have := Nat.lt_floor_add_one (-Real.log t)
    rw [← Real.lt_log_iff_exp_lt h0]
    linarith
  · have := Nat.floor_le hl
    rw [← Real.log_le_iff_le_exp h0]
    linarith

theorem le_two_mul_one_sub_exp_neg {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ε ≤ 2 * (1 - Real.exp (-ε)) := by
  have h2 : ε + 1 ≤ Real.exp ε := Real.add_one_le_exp ε
  have h3 : Real.exp (-ε) * Real.exp ε = 1 := by rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-ε) := Real.exp_pos _
  have h5 : Real.exp (-ε) * (ε + 1) ≤ 1 := by nlinarith
  by_contra hc
  push Not at hc
  nlinarith

theorem mul_lintegral_rpow_le_of_shell_bound :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (h : X → ℝ) (d : ℝ) (B : ℝ≥0∞), Measurable h → (∀ x, 0 < h x) → 0 < d → (∀ j : ℕ, μ {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (d * j))) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ε * ∫⁻ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0) ∂μ ≤ 2 * B := by
  intro X _ μ h d B hm hpos hd hB ε hε0 hε1
  set S : ℕ → Set X := fun j =>
    {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} with hS
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (measurableSet_lt measurable_const hm).inter (measurableSet_le hm measurable_const)
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (Real.exp (-((d + ε) * j))) with hc
  have hpt : ∀ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0)
      ≤ ∑' j, (S j).indicator (fun _ => c j) x := by
    intro x
    split_ifs with hx
    · obtain ⟨j, hj⟩ := exists_shell_of_le_one (hpos x) hx
      refine le_trans ?_ (ENNReal.le_tsum j)
      have hxS : x ∈ S j := hj
      rw [Set.indicator_of_mem hxS]
      apply ENNReal.ofReal_le_ofReal
      calc h x ^ (d + ε) ≤ (Real.exp (-(j : ℝ))) ^ (d + ε) :=
            Real.rpow_le_rpow (hpos x).le hj.2 (by linarith)
        _ = Real.exp (-((d + ε) * j)) := by
            rw [← Real.exp_mul]; congr 1; ring
    · exact zero_le
  set r : ℝ := Real.exp (-ε) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]; linarith
  have hint : ∫⁻ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0) ∂μ
      ≤ B * (1 - ENNReal.ofReal r)⁻¹ := by
    calc _ ≤ ∫⁻ x, ∑' j, (S j).indicator (fun _ => c j) x ∂μ := lintegral_mono hpt
      _ = ∑' j, ∫⁻ x, (S j).indicator (fun _ => c j) x ∂μ :=
          lintegral_tsum fun j => (measurable_const.indicator (hSm j)).aemeasurable
      _ ≤ ∑' j, B * (ENNReal.ofReal r) ^ j := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          rw [lintegral_indicator_const (hSm j)]
          calc c j * μ (S j) ≤ c j * (B * ENNReal.ofReal (Real.exp (d * j))) := by
                gcongr
                exact hB j
            _ = B * (c j * ENNReal.ofReal (Real.exp (d * j))) := by ring
            _ = B * (ENNReal.ofReal r) ^ j := by
                congr 1
                rw [hc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_pow hr0.le,
                  hr, ← Real.exp_add, ← Real.exp_nat_mul]
                congr 2; ring
      _ = B * (1 - ENNReal.ofReal r)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hkey : ENNReal.ofReal ε * (1 - ENNReal.ofReal r)⁻¹ ≤ 2 := by
    have e1 : (1 : ℝ≥0∞) - ENNReal.ofReal r = ENNReal.ofReal (1 - r) := by
      rw [ENNReal.ofReal_sub _ hr0.le, ENNReal.ofReal_one]
    have hp : 0 < 1 - r := by linarith
    rw [e1, ← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_mul hε0.le,
      ← ENNReal.ofReal_ofNat 2]
    apply ENNReal.ofReal_le_ofReal
    rw [← div_eq_mul_inv, div_le_iff₀ hp]
    exact le_two_mul_one_sub_exp_neg hε0 hε1
  calc _ ≤ ENNReal.ofReal ε * (B * (1 - ENNReal.ofReal r)⁻¹) := by gcongr
    _ = (ENNReal.ofReal ε * (1 - ENNReal.ofReal r)⁻¹) * B := by ring
    _ ≤ 2 * B := by gcongr

end GlobalTheory.ResLine
