import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.GeomSum

theorem tsum_zpow_le_rpow_div :
    ∀ (q s Y : ℝ), 1 < q → 0 < s → 0 < Y →
      (∑' n : ℤ, (if q ^ n ≤ Y then ENNReal.ofReal (q ^ (s * (n : ℝ))) else 0))
        ≤ ENNReal.ofReal (Y ^ s / (1 - q ^ (-s))) := by
  intro q s Y hq hs hY
  have hq0 : 0 < q := by linarith
  obtain ⟨N, hN1, hN2⟩ := exists_mem_Ico_zpow hY hq
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = q ^ (-s) := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 ≤ r := hr ▸ (Real.rpow_pos_of_pos hq0 _).le
  have hr1 : r < 1 := hr ▸ Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  let f : ℤ → ℝ≥0∞ := fun n => if n ≤ N then ENNReal.ofReal (q ^ (s * (n : ℝ))) else 0
  have h1 : (∑' n : ℤ, (if q ^ n ≤ Y then ENNReal.ofReal (q ^ (s * (n : ℝ))) else 0))
      ≤ ∑' n, f n := by
    refine ENNReal.tsum_le_tsum fun n => ?_
    by_cases h : q ^ n ≤ Y
    · have h' : n < N + 1 := (zpow_lt_zpow_iff_right₀ hq).1 (lt_of_le_of_lt h hN2)
      have h'' : n ≤ N := by omega
      simp [f, h, h'']
    · simp [h]
  let g : ℕ → ℤ := fun k => N - k
  have hg : Function.Injective g := by
    intro a b h
    simp only [g] at h
    omega
  have hsupp : Function.support f ⊆ Set.range g := by
    intro n hn
    have hnN : n ≤ N := by
      by_contra h
      simp [f, h] at hn
    exact ⟨(N - n).toNat, by simp only [g]; omega⟩
  have h2 : ∑' n, f n = ∑' k : ℕ, f (g k) := (hg.tsum_eq hsupp).symm
  have h3 : ∀ k : ℕ, f (g k) = ENNReal.ofReal (q ^ (s * (N : ℝ)) * r ^ k) := by
    intro k
    have hk : g k ≤ N := by simp only [g]; omega
    simp only [f, hk, if_true]
    congr 1
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]
    congr 1
    simp only [g]
    push_cast
    ring
  have hsum : Summable fun k : ℕ => q ^ (s * (N : ℝ)) * r ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hnn : ∀ k : ℕ, 0 ≤ q ^ (s * (N : ℝ)) * r ^ k := fun k =>
    mul_nonneg (Real.rpow_pos_of_pos hq0 _).le (pow_nonneg hr0 k)
  refine h1.trans ?_
  rw [h2, tsum_congr h3, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum, tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  apply ENNReal.ofReal_le_ofReal
  have hpos : 0 ≤ (1 - r)⁻¹ := inv_nonneg.2 (by linarith)
  refine mul_le_mul_of_nonneg_right ?_ hpos
  have hqN : 0 ≤ q ^ N := (zpow_pos hq0 N).le
  have : q ^ (s * (N : ℝ)) = (q ^ N) ^ s := by
    rw [mul_comm, Real.rpow_mul hq0.le, Real.rpow_intCast]
  rw [this]
  exact Real.rpow_le_rpow hqN hN1 hs.le

end GlobalTheory.CompanionTheory.GeomSum
