import Mathlib

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Filter Asymptotics Finset

namespace SimplexSum

theorem pow_succ_lower (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    x ^ (k + 1) + (k + 1) * x ^ k ≤ (x + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ x ^ k := pow_nonneg hx k
    have h2 : 0 ≤ (k : ℝ) + 1 := by positivity
    rw [show x ^ (k + 1 + 1) = x ^ k * x * x by ring, show (x + 1) ^ (k + 1 + 1) = (x + 1) ^ (k + 1) * (x + 1) by ring,
      show x ^ (k + 1) = x ^ k * x by ring]
    rw [show x ^ (k + 1) = x ^ k * x by ring] at ih
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ x + 1), mul_nonneg h2 h1]

theorem pow_succ_upper (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (x + 1) ^ (k + 1) ≤ x ^ (k + 1) + (k + 1) * (x + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h3 : x ^ (k + 1) ≤ (x + 1) ^ (k + 1) := pow_le_pow_left₀ hx (by linarith) _
    rw [show x ^ (k + 1 + 1) = x ^ (k + 1) * x by ring, show (x + 1) ^ (k + 1 + 1) = (x + 1) ^ (k + 1) * (x + 1) by ring]
    rw [show (x + 1) ^ (k + 1) = (x + 1) ^ k * (x + 1) by ring] at ih h3 ⊢
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ x + 1)]

theorem sum_bounds (k n : ℕ) :
    (n : ℝ) ^ (k + 1) ≤ (k + 1) * ∑ a ∈ range (n + 1), (a : ℝ) ^ k ∧
      (k + 1) * ∑ a ∈ range (n + 1), (a : ℝ) ^ k ≤ (n : ℝ) ^ (k + 1) + (k + 1) * (n : ℝ) ^ k := by
  induction n with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Nat.cast_zero]
    constructor
    · rw [pow_succ, mul_zero]; positivity
    · rw [pow_succ, mul_zero, zero_add]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hl := pow_succ_lower (n : ℝ) hn k
    have hu := pow_succ_upper (n : ℝ) hn k
    push_cast
    constructor <;> nlinarith

def S (i j n : ℕ) : ℝ := ∑ p ∈ antidiagonal n, (p.1 : ℝ) ^ i * (p.2 : ℝ) ^ j

theorem S_zero (i n : ℕ) : S i 0 n = ∑ a ∈ range (n + 1), (a : ℝ) ^ i := by
  unfold S
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp

theorem S_succ (i j n : ℕ) : S i (j + 1) n = n * S i j n - S (i + 1) j n := by
  unfold S
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have : (p.2 : ℝ) = n - p.1 := by rw [← hp]; push_cast; ring
  rw [this]; ring

theorem main (j : ℕ) : ∀ i : ℕ, (fun n : ℕ => S i j n / ((i.factorial : ℝ) * (j.factorial : ℝ)) -
      (n : ℝ) ^ (i + j + 1) / ((i + j + 1).factorial : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (i + j) := by
  induction j with
  | zero =>
    intro i
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    obtain ⟨hb1, hb2⟩ := sum_bounds i n
    simp only [S_zero, Nat.factorial_zero, Nat.cast_one, mul_one, add_zero]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) ^ i), one_mul,
      Nat.factorial_succ]
    push_cast
    have hf : (1 : ℝ) ≤ i.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)
    have hi : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
    have hp : (0 : ℝ) ≤ (n : ℝ) ^ i := by positivity
    set T := ∑ a ∈ range (n + 1), (a : ℝ) ^ i
    have key : T / i.factorial - (n : ℝ) ^ (i + 1) / (((i : ℝ) + 1) * i.factorial) =
        (((i : ℝ) + 1) * T - (n : ℝ) ^ (i + 1)) / (((i : ℝ) + 1) * i.factorial) := by
      field_simp
    rw [key, abs_le]
    constructor
    · have : 0 ≤ (((i : ℝ) + 1) * T - (n : ℝ) ^ (i + 1)) / (((i : ℝ) + 1) * i.factorial) :=
        div_nonneg (by linarith) (by positivity)
      linarith
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hp hi) (by linarith : (0:ℝ) ≤ i.factorial - 1)]
  | succ j ih =>
    intro i
    have h1 := ((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul (ih i)).const_mul_left (1 / ((j : ℝ) + 1))
    have h2 := (ih (i + 1)).const_mul_left (((i : ℝ) + 1) / ((j : ℝ) + 1))
    have h2' : (fun x : ℕ => ((i : ℝ) + 1) / ((j : ℝ) + 1) *
        (S (i + 1) j x / (((i + 1).factorial : ℝ) * (j.factorial : ℝ)) -
          (x : ℝ) ^ (i + 1 + j + 1) / ((i + 1 + j + 1).factorial : ℝ))) =O[atTop]
        fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (i + j) := h2.congr_right (fun n => by ring)
    refine (h1.sub h2').congr' ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      dsimp only
      rw [S_succ]
      rw [show i + (j + 1) + 1 = i + j + 1 + 1 by ring, show i + 1 + j + 1 = i + j + 1 + 1 by ring,
        Nat.factorial_succ (i + j + 1), Nat.factorial_succ j, Nat.factorial_succ i]
      push_cast
      field_simp
      ring
    · refine Eventually.of_forall fun n => ?_
      dsimp only
      ring

end SimplexSum

end ReciprocityTheory.GeometryOfNumbersTheory
