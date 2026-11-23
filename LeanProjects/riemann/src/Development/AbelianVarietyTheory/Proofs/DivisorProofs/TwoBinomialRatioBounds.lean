import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.BinomRatio
open Finset

theorem fact_mul_choose_eq_prod (T a n : ℕ) :
    ((n.factorial : ℕ) : ℝ) * (((T + a + n).choose n : ℕ) : ℝ)
      = ∏ i ∈ range n, ((T : ℝ) + a + 1 + i) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose (T + a) n
  rw [Nat.ascFactorial_eq_prod_range] at h
  have h2 : ((∏ i ∈ range n, (T + a + 1 + i) : ℕ) : ℝ) = ((n.factorial * (T + a + n).choose n : ℕ) : ℝ) := by
    rw [h]
  push_cast at h2
  rw [← h2]

theorem prod_upper (T a n : ℕ) :
    ∏ i ∈ range n, ((T : ℝ) + a + 1 + i)
      ≤ (1 + (a : ℝ) / (T + 1)) ^ n * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
  have hc : (1 + (a : ℝ) / (T + 1)) ^ n = ∏ _i ∈ range n, (1 + (a : ℝ) / (T + 1)) := by simp
  rw [hc, ← prod_mul_distrib]
  apply prod_le_prod
  · intro i _; positivity
  · intro i _
    have hT : (0 : ℝ) < T + 1 := by positivity
    have hi : (0 : ℝ) ≤ i := by positivity
    have ha : (0 : ℝ) ≤ a := by positivity
    have e : (1 + (a : ℝ) / (T + 1)) * ((T : ℝ) + 0 + 1 + i) = (T + 1 + i) + a + a * i / (T + 1) := by
      field_simp; ring
    rw [e]
    have : 0 ≤ (a : ℝ) * i / (T + 1) := by positivity
    linarith

theorem prod_lower (T c n : ℕ) (hc : (c : ℝ) ≤ T) (hT : 0 < T) :
    (1 - (c : ℝ) / T) ^ n * ∏ i ∈ range n, ((T : ℝ) + c + 1 + i)
      ≤ ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hcp : (1 - (c : ℝ) / T) ^ n = ∏ _i ∈ range n, (1 - (c : ℝ) / T) := by simp
  rw [hcp, ← prod_mul_distrib]
  apply prod_le_prod
  · intro i _
    have : (0 : ℝ) ≤ 1 - c / T := by rw [sub_nonneg, div_le_one hT']; exact hc
    positivity
  · intro i _
    have hi : (0 : ℝ) ≤ i := by positivity
    have hc0 : (0 : ℝ) ≤ c := by positivity
    have e : (1 - (c : ℝ) / T) * ((T : ℝ) + c + 1 + i) = (T + 1 + i) - (c * c + c * (1 + i)) / T := by
      field_simp; ring
    rw [e]
    have : 0 ≤ ((c : ℝ) * c + c * (1 + i)) / T := by positivity
    linarith

end GlobalTheory.BinomRatio

namespace GlobalTheory.BinomRatio
open Finset

theorem first_ratio (T n : ℕ) (hn : 2 ≤ n) (hT : 11 * n ^ 2 ≤ T) :
    (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n := by
  have e1 : T + 3 * n + 10 = T + (2 * n + 10) + n := by ring
  have e2 : T + n = T + 0 + n := by ring
  rw [e1, e2]
  have hf : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hA := fact_mul_choose_eq_prod T (2 * n + 10) n
  have hB := fact_mul_choose_eq_prod T 0 n
  have hU := prod_upper T (2 * n + 10) n
  set x : ℝ := ((2 * n + 10 : ℕ) : ℝ) / (T + 1) with hx
  have hT1 : (0 : ℝ) < T + 1 := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hTR : (11 : ℝ) * n ^ 2 ≤ T := by exact_mod_cast hT
  have hnx : (n : ℝ) * x ≤ 0.65 := by
    rw [hx, mul_div_assoc', div_le_iff₀ hT1]
    push_cast
    nlinarith
  have hpow : (1 + x) ^ n ≤ 2 := by
    calc (1 + x) ^ n ≤ (Real.exp x) ^ n := by
          apply pow_le_pow_left₀ (by positivity)
          have := Real.add_one_le_exp x; linarith
      _ = Real.exp (n * x) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (Real.log 2) := by
          apply Real.exp_le_exp.mpr
          have := Real.log_two_gt_d9; linarith
      _ = 2 := Real.exp_log (by norm_num)
  have hP : 0 ≤ ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
    apply prod_nonneg; intro i _; positivity
  have key : ((n.factorial : ℕ) : ℝ) * (((T + (2 * n + 10) + n).choose n : ℕ) : ℝ)
      ≤ ((n.factorial : ℕ) : ℝ) * ((2 * (T + 0 + n).choose n : ℕ) : ℝ) := by
    rw [hA]
    calc ∏ i ∈ range n, ((T : ℝ) + ((2 * n + 10 : ℕ) : ℝ) + 1 + i)
        ≤ (1 + x) ^ n * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := hU
      _ ≤ 2 * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := mul_le_mul_of_nonneg_right hpow hP
      _ = ((n.factorial : ℕ) : ℝ) * ((2 * (T + 0 + n).choose n : ℕ) : ℝ) := by
          push_cast at hB ⊢
          rw [← hB]; ring
  have := le_of_mul_le_mul_left key hf
  exact_mod_cast this

theorem second_ratio (T n : ℕ) (hn : 2 ≤ n) (hT : 11 * n ^ 2 ≤ T) :
    (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) := by
  have e1 : T + 2 * n + 6 = T + (n + 6) + n := by ring
  have e2 : T + n = T + 0 + n := by ring
  rw [e1, e2]
  have hf : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hTR : (11 : ℝ) * n ^ 2 ≤ T := by exact_mod_cast hT
  have hT0 : 0 < T := by nlinarith
  have hTR0 : (0 : ℝ) < T := by exact_mod_cast hT0
  have hc : (((n + 6 : ℕ)) : ℝ) ≤ T := by push_cast; nlinarith
  have hA := fact_mul_choose_eq_prod T (n + 6) n
  have hB := fact_mul_choose_eq_prod T 0 n
  have hL := prod_lower T (n + 6) n hc hT0
  have hbern : 1 + (n : ℝ) * (-((((n + 6 : ℕ)) : ℝ)) / T) ≤ (1 + -((((n + 6 : ℕ)) : ℝ)) / T) ^ n := by
    apply one_add_mul_le_pow
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hTR0]
    linarith
  have hC : (0 : ℝ) ≤ (((T + (n + 6) + n).choose n : ℕ) : ℝ) := by positivity
  have step : (1 - (n : ℝ) * (n + 6) / T) * (((T + (n + 6) + n).choose n : ℕ) : ℝ)
      ≤ (1 - (((n + 6 : ℕ)) : ℝ) / T) ^ n * (((T + (n + 6) + n).choose n : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hC
    have h1 : (1 : ℝ) - (n : ℝ) * (n + 6) / T = 1 + (n : ℝ) * (-((((n + 6 : ℕ)) : ℝ)) / T) := by
      push_cast; ring
    have h2 : (1 : ℝ) - (((n + 6 : ℕ)) : ℝ) / T = 1 + -((((n + 6 : ℕ)) : ℝ)) / T := by ring
    rw [h1, h2]; exact hbern
  have key : ((n.factorial : ℕ) : ℝ) * ((1 - (((n + 6 : ℕ)) : ℝ) / T) ^ n * (((T + (n + 6) + n).choose n : ℕ) : ℝ))
      ≤ ((n.factorial : ℕ) : ℝ) * (((T + 0 + n).choose n : ℕ) : ℝ) := by
    rw [hB, mul_left_comm, hA]
    simpa only [Nat.cast_zero] using hL
  have := le_of_mul_le_mul_left key hf
  linarith

theorem two_binom_ratios : ∀ T n : ℕ, 2 ≤ n → 11 * n ^ 2 ≤ T →
    (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n ∧
    (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) :=
  fun T n hn hT => ⟨first_ratio T n hn hT, second_ratio T n hn hT⟩

end GlobalTheory.BinomRatio
