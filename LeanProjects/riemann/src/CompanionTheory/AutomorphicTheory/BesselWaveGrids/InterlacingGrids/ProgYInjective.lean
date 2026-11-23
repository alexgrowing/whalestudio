import Mathlib

namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

noncomputable def progY (y0 : ℝ) (M : ℕ) : Finset ℝ := (range M).image fun i : ℕ => y0 + 5 * (i : ℝ)

lemma progY_injective (y0 : ℝ) : Function.Injective fun i : ℕ => y0 + 5 * (i : ℝ) := by
  intro i j h
  have : (i : ℝ) = j := by simpa using h
  exact_mod_cast this

theorem progY_card (y0 : ℝ) (M : ℕ) : (progY y0 M).card = M := by
  unfold progY
  rw [card_image_of_injective _ (progY_injective y0), card_range]

theorem progY_sep (y0 : ℝ) (M : ℕ) : ∀ y ∈ progY y0 M, ∀ y' ∈ progY y0 M, y ≠ y' → 5 ≤ |y - y'| := by
  intro y hy y' hy' hne
  simp only [progY, mem_image, mem_range] at hy hy'
  obtain ⟨i, -, rfl⟩ := hy
  obtain ⟨j, -, rfl⟩ := hy'
  have hij : i ≠ j := by
    rintro rfl
    exact hne rfl
  have hsub : y0 + 5 * (i : ℝ) - (y0 + 5 * (j : ℝ)) = 5 * ((i : ℤ) - (j : ℤ) : ℤ) := by
    push_cast; ring
  rw [hsub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5)]
  have h1 : (1 : ℝ) ≤ |(((i : ℤ) - (j : ℤ) : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    have : (1 : ℤ) ≤ |(i : ℤ) - (j : ℤ)| := by
      exact Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hij))
    exact_mod_cast this
  linarith

theorem progY_cut (lo hi : ℝ) (M : ℕ) (hlen : 5 * (M : ℝ) ≤ hi - lo) :
    ∀ y ∈ progY (2 - hi) M, (lo + 2 ≤ -y ∧ -y ≤ hi - 2) ∧ (lo + 2 ≤ -(y + 1) ∧ -(y + 1) ≤ hi - 2) := by
  intro y hy
  simp only [progY, mem_image, mem_range] at hy
  obtain ⟨i, hi', rfl⟩ := hy
  have hiM : (i : ℝ) + 1 ≤ M := by exact_mod_cast hi'
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
