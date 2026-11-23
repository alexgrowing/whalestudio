import Mathlib

open Matrix Finset Real

namespace GlobalTheory

theorem exists_consecutive_ratio_le_rpow :
    ∀ (a q : ℕ) (τ : ℕ → ℝ), 1 ≤ a → a ≤ q → (∀ i ≤ a, 0 < τ i) → (∀ i < a, τ i < τ (i + 1)) →
      τ a = 1 / 2 → ∃ b < a, τ b / τ (b + 1) ≤ (2 * τ 0) ^ ((1 : ℝ) / q) ∧
        τ b ^ 2 ≤ (2 * τ 0) ^ ((1 : ℝ) / q) / 4 := by
  intro a q τ ha haq hpos hinc hta

  have hmono : ∀ j, j ≤ a → ∀ i, i ≤ j → τ i ≤ τ j := by
    intro j
    induction j with
    | zero => intro _ i hi; rw [Nat.le_zero.mp hi]
    | succ n ih =>
      intro hn i hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact (ih (by omega) i (by omega)).trans (hinc n (by omega)).le
      · rw [le_antisymm hi h]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set x := 2 * τ 0 with hx
  have hx0 : 0 < x := by linarith [hpos 0 (Nat.zero_le _)]
  have hx1 : x ≤ 1 := by linarith [hmono a le_rfl 0 (Nat.zero_le _)]
  set r := x ^ ((1 : ℝ) / q) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hx0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one hx0.le hx1 (by positivity)

  have hrq : r ^ q = x := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, one_div_mul_cancel hqpos.ne',
      Real.rpow_one]
  have hra : x ≤ r ^ a := by rw [← hrq]; exact pow_le_pow_of_le_one hr0.le hr1 haq

  obtain ⟨b, hb, hbr⟩ : ∃ b < a, τ b / τ (b + 1) ≤ r := by
    by_contra hne
    push_neg at hne
    have hstep : ∀ b < a, r * τ (b + 1) < τ b := fun b hb => by
      have h1 := hne b hb
      have h2 := hpos (b + 1) (by omega)
      rwa [lt_div_iff₀ h2] at h1
    have hind : ∀ i, i ≤ a → r ^ i * τ i ≤ τ 0 := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        calc r ^ (n + 1) * τ (n + 1) = r ^ n * (r * τ (n + 1)) := by ring
          _ ≤ r ^ n * τ n :=
            mul_le_mul_of_nonneg_left (hstep n (by omega)).le (pow_nonneg hr0.le _)
          _ ≤ τ 0 := ih (by omega)
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    have hlast : r ^ (c + 1) * τ (c + 1) < τ 0 := by
      calc r ^ (c + 1) * τ (c + 1) = r ^ c * (r * τ (c + 1)) := by ring
        _ < r ^ c * τ c := mul_lt_mul_of_pos_left (hstep c (by omega)) (pow_pos hr0 _)
        _ ≤ τ 0 := hind c (by omega)
    rw [hta] at hlast
    linarith
  refine ⟨b, hb, hbr, ?_⟩
  have hb1 : 0 < τ (b + 1) := hpos (b + 1) (by omega)
  have hb0 : 0 < τ b := hpos b (by omega)
  have hle : τ b ≤ r * τ (b + 1) := by rwa [div_le_iff₀ hb1] at hbr
  have hhalf : τ (b + 1) ≤ 1 / 2 := by rw [← hta]; exact hmono a le_rfl (b + 1) (by omega)
  have htb : τ b ≤ r / 2 := by nlinarith [mul_le_mul_of_nonneg_left hhalf hr0.le]
  nlinarith [mul_le_mul htb htb hb0.le (by linarith), mul_le_mul_of_nonneg_left hr1 hr0.le]

end GlobalTheory
