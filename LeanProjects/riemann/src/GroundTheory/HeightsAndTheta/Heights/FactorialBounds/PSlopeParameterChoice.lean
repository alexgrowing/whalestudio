import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

theorem SlopeParameterChoice.proof : SlopeParameterChoice.Statement := by
  intro C₀ C₂ hC₀ hC₂
  refine ⟨9 + C₀ + C₂, ?_⟩
  intro g h μ s hg hh hμ hs
  set K : ℝ := (⌈2 + (g : ℝ) ^ 2 + h⌉₊ : ℝ) with hKdef
  set G : ℝ := (g : ℝ) with hGdef
  set X : ℝ := 2 + G + h with hXdef
  set L : ℝ := Real.log X with hLdef
  have hG1 : (1 : ℝ) ≤ G := by rw [hGdef]; exact_mod_cast hg
  have hKlow : 2 + G ^ 2 + h ≤ K := Nat.le_ceil _
  have hKup : K < 2 + G ^ 2 + h + 1 := Nat.ceil_lt_add_one (by positivity)
  have hGG : G ≤ G ^ 2 := by nlinarith
  have hK3 : (3 : ℝ) ≤ K := by nlinarith
  have hGK : G ≤ K := by nlinarith
  have hhK : h ≤ K := by nlinarith
  have hX3 : (3 : ℝ) ≤ X := by rw [hXdef]; linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hKX : K ≤ X ^ 2 := by rw [hXdef]; nlinarith
  have hlev : (SlopeParameterChoice.level g h : ℝ) = 3 * K := by
    simp only [SlopeParameterChoice.level, hKdef]; push_cast; ring
  have hthird : SlopeParameterChoice.third g h = 3 * K ^ 2 := by
    simp only [SlopeParameterChoice.third, hlev]; ring
  rw [hthird, hlev] at hs

  have hL1 : (1 : ℝ) ≤ L := by
    have he : Real.exp 1 ≤ X := by
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at this

  have hLK : L ≤ K := by
    have : L ≤ X - 1 := Real.log_le_sub_one_of_pos hXpos
    linarith

  have hfirst : 1 / 2 * Real.log (3 * Real.exp 1 * (3 * K ^ 2) ^ 2) ≤ 6 * L := by
    have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have hKpos : (0 : ℝ) < K := by linarith
    have hpos : (0 : ℝ) < 3 * Real.exp 1 * (3 * K ^ 2) ^ 2 := by positivity
    have hK4 : K ^ 4 ≤ X ^ 8 := by
      calc K ^ 4 ≤ (X ^ 2) ^ 4 := pow_le_pow_left₀ hKpos.le hKX 4
        _ = X ^ 8 := by ring
    have hX4 : (81 : ℝ) ≤ X ^ 4 := by
      calc (81 : ℝ) = 3 ^ 4 := by norm_num
        _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX3 4
    have hle : 3 * Real.exp 1 * (3 * K ^ 2) ^ 2 ≤ X ^ 12 := by
      have h1 : 3 * Real.exp 1 * (3 * K ^ 2) ^ 2 ≤ 81 * K ^ 4 := by
        have : 3 * Real.exp 1 * (3 * K ^ 2) ^ 2 = 27 * Real.exp 1 * K ^ 4 := by ring
        rw [this]
        have : (0 : ℝ) ≤ K ^ 4 := by positivity
        nlinarith
      have h2 : 81 * K ^ 4 ≤ X ^ 4 * X ^ 8 :=
        mul_le_mul hX4 hK4 (by positivity) (by positivity)
      calc _ ≤ 81 * K ^ 4 := h1
        _ ≤ X ^ 4 * X ^ 8 := h2
        _ = X ^ 12 := by ring
    have := Real.log_le_log hpos hle
    rw [Real.log_pow] at this
    push_cast at this
    linarith

  have hsecond : 2 / (3 * K ^ 2) * (G * Real.log (3 * K) - μ) ≤ (3 + C₀ + C₂) * L := by
    have hKpos : (0 : ℝ) < K := by linarith
    have hlogm : Real.log (3 * K) ≤ 3 * K := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 3 * K); linarith
    have hKK : K ≤ K ^ 2 := by nlinarith
    have hY : G * Real.log (3 * K) - μ ≤ (7 / 2 + C₀ + C₂) * K ^ 2 := by
      have a1 : G * Real.log (3 * K) ≤ K * (3 * K) :=
        mul_le_mul hGK hlogm (Real.log_nonneg (by linarith)) hKpos.le
      have a3 : C₀ * G ≤ C₀ * K ^ 2 := mul_le_mul_of_nonneg_left (by linarith) hC₀
      have hGL : G * L ≤ K * K := mul_le_mul hGK hLK (by linarith) hKpos.le
      have a4 := mul_le_mul_of_nonneg_left hGL hC₂
      have a5 : C₂ * G * L = C₂ * (G * L) := by ring
      have a6 : K * (3 * K) = 3 * K ^ 2 := by ring
      have a7 : C₂ * (K * K) = C₂ * K ^ 2 := by ring
      have a8 : (7 / 2 + C₀ + C₂) * K ^ 2 = 3 * K ^ 2 + K ^ 2 / 2 + C₀ * K ^ 2 + C₂ * K ^ 2 := by ring
      rw [a8]
      linarith
    have hpos : (0 : ℝ) < 2 / (3 * K ^ 2) := by positivity
    calc 2 / (3 * K ^ 2) * (G * Real.log (3 * K) - μ)
        ≤ 2 / (3 * K ^ 2) * ((7 / 2 + C₀ + C₂) * K ^ 2) :=
          mul_le_mul_of_nonneg_left hY hpos.le
      _ = 2 / 3 * (7 / 2 + C₀ + C₂) := by field_simp
      _ ≤ 3 + C₀ + C₂ := by linarith
      _ ≤ (3 + C₀ + C₂) * L := le_mul_of_one_le_right (by linarith) hL1
  calc s ≤ _ := hs
    _ ≤ 6 * L + (3 + C₀ + C₂) * L := add_le_add hfirst hsecond
    _ = (9 + C₀ + C₂) * L := by ring

end

end GroundTheory.Heights₂.Heights
