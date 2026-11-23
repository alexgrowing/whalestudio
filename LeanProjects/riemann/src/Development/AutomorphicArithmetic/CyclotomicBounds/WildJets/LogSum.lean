import Mathlib

theorem UpperTheory.WildA.logSum :
    ∀ y : ℝ, 1 ≤ y → ∑ l ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, Real.logb l y * Real.log l ≤ y * Real.log y := by
  intro y hy
  set S := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime with hS
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hterm : ∀ l ∈ S, Real.logb l y * Real.log l = Real.log y := by
    intro l hl
    have hp : Nat.Prime l := (Finset.mem_filter.1 hl).2
    have h1 : (1:ℝ) < l := by exact_mod_cast hp.one_lt
    have hlog : Real.log l ≠ 0 := (Real.log_pos h1).ne'
    rw [Real.logb, div_mul_cancel₀ _ hlog]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hlogy
  have hsub : S ⊆ (Finset.range (⌊y⌋₊ + 1)).erase 0 := by
    intro l hl
    rw [hS, Finset.mem_filter] at hl
    exact Finset.mem_erase.2 ⟨hl.2.ne_zero, hl.1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (by simp), Finset.card_range] at hcard
  have h2 : S.card ≤ ⌊y⌋₊ := by omega
  calc (S.card : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h2
    _ ≤ y := Nat.floor_le (by linarith)
