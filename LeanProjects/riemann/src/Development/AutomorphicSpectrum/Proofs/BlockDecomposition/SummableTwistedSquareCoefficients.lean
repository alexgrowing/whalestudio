import Mathlib

namespace GlobalTheory.CompanionTheory.LSeriesBound

theorem lseriesSummable_twist_squares (M N k : ℕ) [NeZero M] (hM : N ∣ M)
    (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (hk : 1 ≤ k)
    (hb : ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ 2 * (n : ℝ) * (n : ℝ) ^ (k - 1))
    (s : ℂ) (hs : 2 < s.re) :
    LSeriesSummable (fun n : ℕ => DirichletCharacter.changeLevel hM χ⁻¹ (n : ZMod M) * a (n ^ 2))
      (s + k - 1) := by
  have hre : (s + (k : ℂ) - 1).re = s.re + (k : ℝ) - 1 := by simp
  have hsum : Summable (fun n : ℕ => 2 * (n : ℝ) ^ (1 - s.re)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left 2
  refine Summable.of_norm_bounded hsum (fun n => ?_)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hf : ‖DirichletCharacter.changeLevel hM χ⁻¹ (n : ZMod M) * a (n ^ 2)‖
      ≤ 2 * (n : ℝ) ^ k := by
    by_cases hu : IsUnit (n : ZMod M)
    · have hcop : Nat.Coprime n M := (ZMod.isUnit_iff_coprime n M).mp hu
      have hcopN : Nat.Coprime n N := Nat.Coprime.coprime_dvd_right hM hcop
      have h1 : ‖DirichletCharacter.changeLevel hM χ⁻¹ (n : ZMod M)‖ ≤ 1 :=
        DirichletCharacter.norm_le_one _ _
      have h2 := hb n hcopN
      have h3 : 2 * (n : ℝ) * (n : ℝ) ^ (k - 1) = 2 * (n : ℝ) ^ k := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        ring
      rw [norm_mul]
      calc _ ≤ 1 * ‖a (n ^ 2)‖ := by gcongr
        _ ≤ 2 * (n : ℝ) ^ k := by rw [one_mul, ← h3]; exact h2
    · rw [MulChar.map_nonunit _ hu]
      simp only [zero_mul, norm_zero]
      positivity
  rw [hre, div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)]
  have hpow : (n : ℝ) ^ (1 - s.re) * (n : ℝ) ^ (s.re + (k : ℝ) - 1) = (n : ℝ) ^ k := by
    rw [← Real.rpow_add hn0, ← Real.rpow_natCast]
    congr 1
    ring
  calc _ ≤ 2 * (n : ℝ) ^ k := hf
    _ = _ := by rw [← hpow]; ring

end GlobalTheory.CompanionTheory.LSeriesBound
