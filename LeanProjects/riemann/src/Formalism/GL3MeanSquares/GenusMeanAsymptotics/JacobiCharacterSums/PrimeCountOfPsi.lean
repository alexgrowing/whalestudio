import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTEOf
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiC

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem prime_count_of_psi : PiOf := by
  rintro ⟨c, A, C₀, hc, hP⟩
  obtain ⟨c₁, hc₁, hηl⟩ := etaOf_lower 1 one_pos
  refine ⟨min (c / 2) (c ^ 2 / 2), 10 * |A| + 5632 * Real.exp (2 * min (c / 2) (c ^ 2 / 2)) / c₁,
    max (2 * C₀) 16, lt_min (by positivity) (by positivity), ?_⟩
  intro M _ h8
  refine ⟨eOf M, fun p hp => eOf_exc M p hp, fun h χ₁ β₁ => eOf_none M h χ₁ β₁, ?_⟩
  intro X b hX2 hrange hb
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM8n : 8 ≤ M := Nat.le_of_dvd hMpos h8
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast hM8n
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl : 2 ≤ Real.log M := by
    have h88 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hM8
    linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hll : 1 ≤ Real.log (Real.log M + 2) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ Real.log M + 2)
    linarith
  have hprod : Real.log M ≤ Real.log M * Real.log (Real.log M + 2) := by nlinarith
  have hprod0 : 0 ≤ Real.log M * Real.log (Real.log M + 2) := by linarith
  have hrange' : max (2 * C₀) 16 * (Real.log M * Real.log (Real.log M + 2)) ≤ Real.log X := by
    rw [← mul_assoc]; exact hrange
  have hL16 : 16 * Real.log M ≤ Real.log X := by
    have := mul_le_mul_of_nonneg_right (le_max_right (2 * C₀) 16) hprod0
    linarith
  have hLC : C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X / 2 := by
    have := mul_le_mul_of_nonneg_right (le_max_left (2 * C₀) 16) hprod0
    have e : C₀ * Real.log M * Real.log (Real.log M + 2) =
        2 * C₀ * (Real.log M * Real.log (Real.log M + 2)) / 2 := by ring
    rw [e]
    linarith
  have hX0 : 0 < X := by linarith
  have hX4 : 4 ≤ X := by
    rw [← Real.log_le_log_iff (by norm_num) hX0]
    linarith
  have hs2 : 2 ≤ √X := by
    rw [Real.le_sqrt' (by norm_num)]; linarith
  have hη0 : 0 ≤ etaOf M := (etaOf_pos M (by omega)).le
  have hη1 := etaOf_le_one M
  have hηl' := hηl M (by omega)
  have hP' : ∀ y : ℝ, √X ≤ y → y ≤ X →
      ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      |A| * y * etaOf M *
        (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y)))) := by
    intro y h1 h2
    have hy2 : 2 ≤ y := hs2.trans h1
    have hly : Real.log X / 2 ≤ Real.log y := by
      rw [← Real.log_sqrt hX0.le]
      exact Real.log_le_log (by linarith) h1
    refine (hP M h8 y hy2 (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)) hη0) (by positivity)
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [he] at hP'
    have e0 : mainAP (none : Option (DirichletCharacter ℂ M × ℝ)) b X =
        (liX X - 0 * liX (X ^ (1 : ℝ))) / (M.totient : ℝ) := by simp [mainAP]
    rw [e0]
    exact pi_core M h8 b hb none (by simp) (by norm_num) le_rfl
      (fun t _ => mainPsi_sum_none M b hb t 1) hη0 hη1 (Or.inl le_rfl) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'
  · rw [he] at hP'
    obtain ⟨_, _, _, hβlo, hβ1⟩ := eOf_exc M _ he
    have hχ := eOf_char_sq M χ₁ β₁ he b ((ZMod.isUnit_iff_coprime b M).mpr hb)
    have hθ : |(χ₁ (b : ZMod M)).re| ≤ 1 := by rcases hχ with h | h <;> simp [h]
    have hβ : 1 / 2 ≤ β₁ := by
      have : 1 / (8 * Real.log M) ≤ 1 / 16 := by
        apply one_div_le_one_div_of_le (by norm_num); linarith
      simp only [] at hβlo
      linarith
    have hηe := etaOf_some M χ₁ β₁ he
    have e1 : mainAP (some (χ₁, β₁)) b X =
        (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ) := rfl
    rw [e1]
    exact pi_core M h8 b hb (some (χ₁, β₁)) hθ hβ hβ1.le
      (fun t ht => mainPsi_sum_some M b hb χ₁ β₁ t ht hχ) hη0 hη1
      (Or.inr (by rw [hηe]; exact min_le_right _ _)) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'

end Formalism.HermitianLattices.Ext.PrimesInProgressions
