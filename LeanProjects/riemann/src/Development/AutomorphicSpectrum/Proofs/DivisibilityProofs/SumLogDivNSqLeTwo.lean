import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem log_tail_step (x : ℝ) (hx : 1 ≤ x) :
    Real.log (x + 1) / ((x + 1) * x) ≤
      (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hL : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    have he : (x + 1) / x - 1 = 1 / x := by
      field_simp
      ring
    linarith
  have hK : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ 2 := by
    have h1 : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ (x + 1) * (1 / x) :=
      mul_le_mul_of_nonneg_left hL (by linarith)
    have h2 : (x + 1) * (1 / x) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hx0]
      linarith
    linarith
  have hE : (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) - Real.log (x + 1) / ((x + 1) * x) =
      (2 - (x + 1) * (Real.log (x + 1) - Real.log x)) / ((x + 1) * x) := by
    field_simp
    ring
  have hpos : 0 ≤ (2 - (x + 1) * (Real.log (x + 1) - Real.log x)) / ((x + 1) * x) :=
    div_nonneg (by linarith) (by positivity)
  linarith

theorem log_tail_Icc (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤
      2 - (Real.log N + 2) / N := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by norm_num)]
    simp
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hstep := log_tail_step (k : ℝ) (by exact_mod_cast hk)
    have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hc]
    have hc2 : (k : ℝ) + 1 - 1 = k := by ring
    rw [hc2]
    linarith

theorem log_tail :
    ∀ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) →
      ∑ n ∈ S, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 := by
  intro S hS
  have hN : 1 ≤ max 1 (S.sup id) := le_max_left _ _
  have hsub : S ⊆ Finset.Icc 2 (max 1 (S.sup id)) := by
    intro n hn
    rw [Finset.mem_Icc]
    exact ⟨hS n hn, le_trans (Finset.le_sup (f := id) hn) (le_max_right _ _)⟩
  have hnn : ∀ n ∈ Finset.Icc 2 (max 1 (S.sup id)), 0 ≤ Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith
  have h1 : (1 : ℝ) ≤ ((max 1 (S.sup id) : ℕ) : ℝ) := by exact_mod_cast hN
  have hq : 0 ≤ (Real.log ((max 1 (S.sup id) : ℕ) : ℝ) + 2) / ((max 1 (S.sup id) : ℕ) : ℝ) :=
    div_nonneg (by linarith [Real.log_nonneg h1]) (by linarith)
  calc ∑ n ∈ S, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
      ≤ ∑ n ∈ Finset.Icc 2 (max 1 (S.sup id)), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hnn n hn)
    _ ≤ 2 - (Real.log ((max 1 (S.sup id) : ℕ) : ℝ) + 2) / ((max 1 (S.sup id) : ℕ) : ℝ) :=
        log_tail_Icc _ hN
    _ ≤ 2 := by linarith

end GlobalTheory.CompanionTheory.Ar.Small
