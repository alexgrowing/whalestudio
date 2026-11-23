import Mathlib
import Formalism.PeriodIntegrals.GeometricProductPowers.GaussianProductPowerBound

namespace GeoProdPow

open Finset

theorem one_sub_sum_le_prod (s : Finset ℕ) (u a : ℕ → ℝ) (h0 : ∀ i ∈ s, 0 ≤ u i)
    (h1 : ∀ i ∈ s, u i ≤ 1) (ha : ∀ i ∈ s, 1 - a i ≤ u i) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, u i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have hP1 : ∏ i ∈ s, u i ≤ 1 :=
      Finset.prod_le_one (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hP := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have hu1 := h1 j (Finset.mem_insert_self j s)
    have hua := ha j (Finset.mem_insert_self j s)
    nlinarith [mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hP1)]

theorem geom_le (g : ℝ) (hg : 1 < g) (r : ℕ) :
    ∑ i ∈ Ico 1 r, (g⁻¹) ^ i ≤ 1 / (g - 1) := by
  have hg0 : (0 : ℝ) < g := by linarith
  have hlt : g⁻¹ < 1 := inv_lt_one_of_one_lt₀ hg
  have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := r) (inv_nonneg.2 hg0.le) hlt
  have he : g⁻¹ ^ 1 / (1 - g⁻¹) = 1 / (g - 1) := by
    have h1 : g - 1 ≠ 0 := by linarith
    field_simp
  linarith [he ▸ h]

theorem factor (g : ℝ) (hg : 0 < g) (i : ℕ) : g ^ i - 1 = g ^ i * (1 - (g⁻¹) ^ i) := by
  rw [inv_pow, mul_sub, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hg.ne')]

theorem gauss (r : ℕ) : ∑ i ∈ Ico 1 r, i = r * (r - 1) / 2 := by
  rcases r with _ | r
  · simp
  · rw [← Finset.sum_range_id, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos r)]
    simp

theorem prod_split (g0 g1 : ℝ) (h0 : 0 < g0) (h1 : 0 < g1) (r : ℕ) :
    ∏ i ∈ Ico 1 r, ((g0 ^ i - 1) * (g1 ^ i - 1)) =
      (g0 * g1) ^ (r * (r - 1) / 2) *
        ∏ i ∈ Ico 1 r, ((1 - (g0⁻¹) ^ i) * (1 - (g1⁻¹) ^ i)) := by
  have e : ∀ i, (g0 ^ i - 1) * (g1 ^ i - 1) =
      (g0 * g1) ^ i * ((1 - (g0⁻¹) ^ i) * (1 - (g1⁻¹) ^ i)) := by
    intro i
    rw [factor g0 h0 i, factor g1 h1 i, mul_pow]
    ring
  have hp := Finset.prod_pow_eq_pow_sum (Ico 1 r) (fun i => i) (g0 * g1)
  rw [Finset.prod_congr rfl (fun i _ => e i), Finset.prod_mul_distrib, hp, gauss]

theorem one_sub_pow_mem (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (i : ℕ) :
    0 ≤ 1 - x ^ i ∧ 1 - x ^ i ≤ 1 :=
  ⟨sub_nonneg.2 (pow_le_one₀ h0 h1), by linarith [pow_nonneg h0 i]⟩

theorem main : ConditionalKappaBounds.G2.GaussianProductPowerBound := by
  intro f k r b g0 g1 hf hfk hb hg0 hg1
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hf.trans hfk
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hfk' : (f : ℝ) ≤ k := by exact_mod_cast hfk
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 256 * (k : ℝ) ^ 8 - 1 := ⟨_, rfl⟩
  have hk8 : (1 : ℝ) ≤ (k : ℝ) ^ 8 := one_le_pow₀ hk
  have hG : 256 * (k : ℝ) ^ 8 ≤ ((k : ℝ) * b) ^ 8 := by
    rw [mul_pow]
    have hb8 : (2 : ℝ) ^ 8 ≤ b ^ 8 := pow_le_pow_left₀ (by norm_num) hb 8
    nlinarith
  have hD255 : 255 ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hA0 : D + 1 ≤ g0 := by linarith
  have hA1 : D + 1 ≤ g1 := by linarith
  have hg0p : 0 < g0 := by linarith
  have hg1p : 0 < g1 := by linarith
  have hs0 : ∑ i ∈ Ico 1 r, (g0⁻¹) ^ i ≤ 1 / D :=
    (geom_le g0 (by linarith) r).trans (one_div_le_one_div_of_le hDpos (by linarith))
  have hs1 : ∑ i ∈ Ico 1 r, (g1⁻¹) ^ i ≤ 1 / D :=
    (geom_le g1 (by linarith) r).trans (one_div_le_one_div_of_le hDpos (by linarith))
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ i ∈ Ico 1 r, ((g0⁻¹) ^ i + (g1⁻¹) ^ i) := ⟨_, rfl⟩
  have hS : S ≤ 2 / D := by
    have e2 : 2 / D = 1 / D + 1 / D := by ring
    rw [hSdef, Finset.sum_add_distrib, e2]
    linarith
  have h2D : 2 / D ≤ 1 := (div_le_one hDpos).2 (by linarith)
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ∏ i ∈ Ico 1 r, ((1 - (g0⁻¹) ^ i) * (1 - (g1⁻¹) ^ i)) :=
    ⟨_, rfl⟩
  have hx0 : 0 ≤ g0⁻¹ := inv_nonneg.2 hg0p.le
  have hx1 : 0 ≤ g1⁻¹ := inv_nonneg.2 hg1p.le
  have hy0 : g0⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hy1 : g1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hP : 1 - S ≤ P := by
    rw [hSdef, hPdef]
    apply one_sub_sum_le_prod
    · intro i _
      exact mul_nonneg (one_sub_pow_mem _ hx0 hy0 i).1 (one_sub_pow_mem _ hx1 hy1 i).1
    · intro i _
      exact mul_le_one₀ (one_sub_pow_mem _ hx0 hy0 i).2 (one_sub_pow_mem _ hx1 hy1 i).1
        (one_sub_pow_mem _ hx1 hy1 i).2
    · intro i _
      nlinarith [mul_nonneg (pow_nonneg hx0 i) (pow_nonneg hx1 i)]
  have hS0 : 0 ≤ 1 - S := by linarith
  have hB : 1 + (f : ℝ) * (-S) ≤ (1 + -S) ^ f := one_add_mul_le_pow (by linarith) f
  have hPf : (1 - S) ^ f ≤ P ^ f := pow_le_pow_left₀ hS0 hP f
  have hf4 : (f : ℝ) ^ 4 ≤ (k : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) hfk' 4
  have hk87 : (k : ℝ) ^ 7 ≤ (k : ℝ) ^ 8 := pow_le_pow_right₀ hk (by norm_num)
  have hk7 : (1 : ℝ) ≤ (k : ℝ) ^ 7 := one_le_pow₀ hk
  have hfk3 : (f : ℝ) ^ 4 * (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 7 := by
    calc (f : ℝ) ^ 4 * (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 4 * (k : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hf4 (by positivity)
      _ = (k : ℝ) ^ 7 := by ring
  have key : 2 * (f : ℝ) / D ≤ 1 / (4 * ((f : ℝ) * k) ^ 3) := by
    rw [div_le_div_iff₀ hDpos (by positivity)]
    have e : 2 * (f : ℝ) * (4 * ((f : ℝ) * k) ^ 3) = 8 * ((f : ℝ) ^ 4 * (k : ℝ) ^ 3) := by ring
    rw [e]
    linarith
  have hfS : (f : ℝ) * S ≤ 2 * (f : ℝ) / D := by
    have : (f : ℝ) * S ≤ (f : ℝ) * (2 / D) := mul_le_mul_of_nonneg_left hS (by linarith)
    linarith [show (f : ℝ) * (2 / D) = 2 * (f : ℝ) / D by ring]
  have hinv : (((f : ℝ) * k) ^ 3)⁻¹ / 4 = 1 / (4 * ((f : ℝ) * k) ^ 3) := by ring
  have hc : 1 - (((f : ℝ) * k) ^ 3)⁻¹ / 4 ≤ P ^ f := by
    rw [hinv]
    have : (1 + -S) = 1 - S := by ring
    rw [this] at hB
    linarith
  rw [prod_split g0 g1 hg0p hg1p r, ← hPdef]
  have e : ((g0 * g1) ^ (r * (r - 1) / 2) * P) ^ f =
      P ^ f * (g0 * g1) ^ (f * (r * (r - 1) / 2)) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (r * (r - 1) / 2) f,
      mul_comm ((g0 * g1) ^ (f * (r * (r - 1) / 2)))]
  rw [e]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

end GeoProdPow
