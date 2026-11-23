import Mathlib
import Formalism.PeriodIntegrals.LpLower

namespace PI

open Finset

theorem lp_shift_sum (d : ℕ) [NeZero d] (xs : ZMod d → ℕ → ℝ) :
    ∑ s, ∑ i ∈ range d, xs (s - (i : ZMod d)) i = ∑ s, ∑ i ∈ range d, xs s i := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => rfl)

theorem lp_feasible_le (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (hl : 2 ≤ l)
    {y : ℝ} (hy : y ∈ lpFeasible l d Ds) : y ≤ (∑ s, Ds s) / ((l : ℝ) + 1) := by
  obtain ⟨xs, h0, hsupp, hc, rfl⟩ := hy
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (by omega : 1 ≤ l)
  have hsum : ∑ s, ((∑ i ∈ range d, (l : ℝ) ^ i * xs s i) +
      (∑ i ∈ range d, xs (s - (i : ZMod d)) i)) ≤ ∑ s, Ds s :=
    Finset.sum_le_sum fun s _ => hc s
  rw [Finset.sum_add_distrib, lp_shift_sum] at hsum
  have hlow : (l : ℝ) * ∑ s, ∑ i ∈ range d, xs s i ≤
      ∑ s, ∑ i ∈ range d, (l : ℝ) ^ i * xs s i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : Odd i
    · have hi0 : i ≠ 0 := by
        rintro rfl
        simp at hi
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (h0 s i)
    · rw [hsupp s i (Or.inl hi)]
      simp
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hsum, hlow]

theorem lp_zero_mem (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (hD : ∀ s, 0 ≤ Ds s) :
    (0 : ℝ) ∈ lpFeasible l d Ds :=
  ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ _ _ => rfl, fun s => by simpa using hD s, by simp⟩

theorem lpLower_main : LpLower := by
  intro l d _ Ds hl hD
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hsup : sSup (lpFeasible l d Ds) ≤ (∑ s, Ds s) / ((l : ℝ) + 1) :=
    csSup_le ⟨0, lp_zero_mem l d Ds hD⟩ fun y hy => lp_feasible_le l d Ds hl hy
  have h1 : (l : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (l : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (l : ℝ) - 1 := by linarith
    exact this.ne'
  have h3 : (l : ℝ) ^ 2 - 1 ≠ 0 := by
    have : (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) := by ring
    rw [this]
    exact mul_ne_zero h2 h1
  have hid : (l : ℝ) / ((l : ℝ) ^ 2 - 1) * (∑ s, Ds s) - (∑ s, Ds s) / ((l : ℝ) + 1) =
      (∑ s, Ds s) / ((l : ℝ) ^ 2 - 1) := by
    have h4 : (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) := by ring
    rw [h4]
    field_simp
    ring
  unfold lpF
  linarith

end PI
