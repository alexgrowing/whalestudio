import Mathlib

noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

theorem lmajASeq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
    (f : Fin k → SchwartzMap V ℂ) (q : V → ℝ) (hq0 : ∀ y, 0 ≤ q y) (A : ℝ) (hA : 0 ≤ A)
    (hqA : ∀ y, q y ≤ A * ‖y‖ ^ 2) :
    ∃ b : ℕ → ℝ, (∀ n, 0 ≤ b n) ∧ (∀ j : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ j)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i y, (N : ℝ) ≤ q y → ‖f i y‖ ≤ ε * b ⌊q y⌋₊ := by
  set S : ℕ → ℝ := fun j => ∑ i, (Finset.Iic (2 * j, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (f i) with hS
  set D : ℕ → ℝ := fun j => (1 + A) ^ j * (2 ^ (2 * j) * S j) with hDdef
  have hS0 : ∀ j, 0 ≤ S j := fun j => Finset.sum_nonneg fun i _ => apply_nonneg _ _
  have hD0 : ∀ j, 0 ≤ D j := fun j =>
    mul_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (by positivity) (hS0 j))
  have hD : ∀ j i y, (1 + q y) ^ j * ‖f i y‖ ≤ D j := by
    intro j i y
    have h1 : 1 + q y ≤ (1 + A) * (1 + ‖y‖) ^ 2 := by
      have := hqA y; have hy := norm_nonneg y; nlinarith [mul_nonneg hA hy]
    have h2 : (1 + ‖y‖) ^ (2 * j) * ‖f i y‖ ≤ 2 ^ (2 * j) * S j := by
      have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2 * j, 0)) (k := 2 * j)
        (n := 0) le_rfl le_rfl (f i) y
      rw [norm_iteratedFDeriv_zero] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Finset.single_le_sum (f := fun i => (Finset.Iic (2 * j, 0)).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (f i)) (fun i _ => apply_nonneg _ _)
        (Finset.mem_univ i)
    calc (1 + q y) ^ j * ‖f i y‖ ≤ ((1 + A) * (1 + ‖y‖) ^ 2) ^ j * ‖f i y‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith [hq0 y]) h1 j) (norm_nonneg _)
      _ = (1 + A) ^ j * ((1 + ‖y‖) ^ (2 * j) * ‖f i y‖) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ D j := mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) _)
  set m : ℕ → ℝ := fun n => ⨅ j : ℕ, D j / (1 + (n : ℝ)) ^ j with hm
  have hbdd : ∀ n : ℕ, BddBelow (Set.range fun j : ℕ => D j / (1 + (n : ℝ)) ^ j) :=
    fun n => ⟨0, by rintro _ ⟨j, rfl⟩; exact div_nonneg (hD0 j) (by positivity)⟩
  have hm0 : ∀ n, 0 ≤ m n := fun n => le_ciInf fun j => div_nonneg (hD0 j) (by positivity)
  have hmle : ∀ n j, m n ≤ D j / (1 + (n : ℝ)) ^ j := fun n j => ciInf_le (hbdd n) j
  have hfm : ∀ i y, ‖f i y‖ ≤ m ⌊q y⌋₊ := by
    intro i y
    refine le_ciInf fun j => ?_
    rw [le_div_iff₀ (by positivity)]
    have hn : (⌊q y⌋₊ : ℝ) ≤ q y := Nat.floor_le (hq0 y)
    calc ‖f i y‖ * (1 + (⌊q y⌋₊ : ℝ)) ^ j ≤ (1 + q y) ^ j * ‖f i y‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j)
            (norm_nonneg _)
      _ ≤ D j := hD j i y
  set b : ℕ → ℝ := fun n => Real.sqrt (m n) with hb
  have hbdec : ∀ j n, b n ≤ Real.sqrt (D (2 * j)) / (1 + (n : ℝ)) ^ j := by
    intro j n
    have hpos : 0 < (1 + (n : ℝ)) ^ j := by positivity
    calc b n ≤ Real.sqrt (D (2 * j) / (1 + (n : ℝ)) ^ (2 * j)) := Real.sqrt_le_sqrt (hmle n (2 * j))
      _ = Real.sqrt (D (2 * j)) / (1 + (n : ℝ)) ^ j := by
          rw [Real.sqrt_div (hD0 _), pow_mul', Real.sqrt_sq hpos.le]
  have hsum2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    refine ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).congr
      fun n => ?_
    push_cast; ring
  have hbs : ∀ j : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ j) := by
    intro j
    refine (hsum2.mul_left (Real.sqrt (D (2 * (j + 2))) * 2 ^ j)).of_nonneg_of_le
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (fun n => ?_)
    have hpos : 0 < (1 + (n : ℝ)) := by positivity
    have h1 := hbdec (j + 2) n
    have h2 : ((n : ℝ) + 2) ^ j ≤ 2 ^ j * (1 + (n : ℝ)) ^ j := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) j
    calc b n * ((n : ℝ) + 2) ^ j ≤ Real.sqrt (D (2 * (j + 2))) / (1 + (n : ℝ)) ^ (j + 2) *
          (2 ^ j * (1 + (n : ℝ)) ^ j) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = Real.sqrt (D (2 * (j + 2))) * 2 ^ j * (1 / ((n : ℝ) + 1) ^ 2) := by
          field_simp; ring
  refine ⟨b, fun n => Real.sqrt_nonneg _, hbs, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt (D (2 * 1)) / ε)
  refine ⟨N, fun i y hy => ?_⟩
  have hNn : N ≤ ⌊q y⌋₊ := Nat.le_floor hy
  have hbε : b ⌊q y⌋₊ ≤ ε := by
    have h1 := hbdec 1 ⌊q y⌋₊
    rw [pow_one] at h1
    have hNr : (N : ℝ) ≤ (⌊q y⌋₊ : ℝ) := by exact_mod_cast hNn
    have h3 := (div_lt_iff₀ hε).mp hN
    have h4 : Real.sqrt (D (2 * 1)) / (1 + (⌊q y⌋₊ : ℝ)) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  calc ‖f i y‖ ≤ m ⌊q y⌋₊ := hfm i y
    _ = b ⌊q y⌋₊ * b ⌊q y⌋₊ := (Real.mul_self_sqrt (hm0 _)).symm
    _ ≤ ε * b ⌊q y⌋₊ := mul_le_mul_of_nonneg_right hbε (Real.sqrt_nonneg _)

end PositivityTheory.Rg.Rsw.L.LMajor

end
