import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PairBdNonneg
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.AmpArith

theorem v_part (k r f j : ℕ) (v : ℝ) (hr : 1 ≤ r) (hv : 1 ≤ v) :
    v ^ (k * (r - j) * f) *
        ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f
      ≤ 2 ^ (r ^ 2 * f) := by
  have hv0 : v ≠ 0 := by positivity
  have h2v : 0 ≤ 2 * v := by positivity
  have hexp : r * (k + 1) + r * (r - 1) = r * k + r ^ 2 := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  have hneg : (2 * v) ^ (-((r : ℝ) * k)) = ((2 * v) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg h2v, show ((r : ℝ) * k) = ((r * k : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have key : ((2 * v) ^ (r * k))⁻¹ * 1 * (2 : ℝ) ^ (r * k + r ^ 2) = 2 ^ (r ^ 2) / v ^ (r * k) := by
    rw [mul_pow, pow_add]
    field_simp
  have hle : v ^ (k * (r - j) * f) ≤ v ^ (r * k * f) := by
    apply pow_le_pow_right₀ hv
    have : r - j ≤ r := Nat.sub_le r j
    calc k * (r - j) * f ≤ k * r * f := by gcongr
    _ = r * k * f := by ring
  rw [hneg, hexp, key, div_pow, ← pow_mul, ← pow_mul, mul_div_assoc', div_le_iff₀ (by positivity)]
  calc v ^ (k * (r - j) * f) * 2 ^ (r ^ 2 * f) ≤ v ^ (r * k * f) * 2 ^ (r ^ 2 * f) := by gcongr
  _ = 2 ^ (r ^ 2 * f) * v ^ (r * k * f) := by ring

theorem exponent_bound (CH C R F : ℝ) (hCH : 0 ≤ CH) (hC : 100 * (CH + 10) ≤ C) (hR : 1 ≤ R)
    (hF : 0 ≤ F) :
    R ^ 2 * F + 3 * (2 * (R + 1) ^ 2 * F) + 3 * (2 * (R + 1) ^ 2 * F)
        + ((2 * R + 2) + 3 + CH * (2 * R + 2)) * (80 * R ^ 4 * F)
      ≤ C * (2 * R + 2) ^ 2 * F * (C * R ^ 4) := by
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR4 : R ^ 2 ≤ R ^ 4 := by nlinarith
  have hR41 : 1 ≤ R ^ 4 := le_trans hR2 hR4
  have hS : 1 ≤ (R + 1) ^ 2 := by nlinarith
  have hP0 : 0 ≤ R ^ 4 * (R + 1) ^ 2 := by positivity
  have e1 : R ^ 2 ≤ R ^ 4 * (R + 1) ^ 2 := by
    calc R ^ 2 ≤ R ^ 4 := hR4
    _ = R ^ 4 * 1 := by ring
    _ ≤ R ^ 4 * (R + 1) ^ 2 := by gcongr
  have e2 : (R + 1) ^ 2 ≤ R ^ 4 * (R + 1) ^ 2 := by
    calc (R + 1) ^ 2 = 1 * (R + 1) ^ 2 := by ring
    _ ≤ R ^ 4 * (R + 1) ^ 2 := by gcongr
  have e3 : R ^ 4 * (2 * R + 5) ≤ 5 * (R ^ 4 * (R + 1) ^ 2) := by
    have : 2 * R + 5 ≤ 5 * (R + 1) ^ 2 := by nlinarith
    calc R ^ 4 * (2 * R + 5) ≤ R ^ 4 * (5 * (R + 1) ^ 2) := by gcongr
    _ = 5 * (R ^ 4 * (R + 1) ^ 2) := by ring
  have e4 : R ^ 4 * (2 * R + 2) ≤ 2 * (R ^ 4 * (R + 1) ^ 2) := by
    have : 2 * R + 2 ≤ 2 * (R + 1) ^ 2 := by nlinarith
    calc R ^ 4 * (2 * R + 2) ≤ R ^ 4 * (2 * (R + 1) ^ 2) := by gcongr
    _ = 2 * (R ^ 4 * (R + 1) ^ 2) := by ring
  have hC1 : 1000 ≤ C := by linarith
  have hCC : 413 + 160 * CH ≤ 4 * C ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left e1 hF, mul_le_mul_of_nonneg_left e2 hF,
    mul_le_mul_of_nonneg_left e3 hF, mul_le_mul_of_nonneg_left e4 (mul_nonneg hF hCH),
    mul_le_mul_of_nonneg_left hCC (mul_nonneg hF hP0)]

theorem b_part (CH C : ℝ) (hCH : 0 ≤ CH) (hC : 100 * (CH + 10) ≤ C) (r m f : ℕ) (b v : ℝ)
    (hm : m = 2 * r + 2) (hr : 1 ≤ r) (hb : 2 ≤ b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b) :
    2 ^ (r ^ 2 * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)
        * (8 * r * b ^ (CH * m)) ^ (80 * r ^ 4 * f)
      ≤ (b ^ (C * (m : ℝ) ^ 2 * f)) ^ (C * (r : ℝ) ^ 4) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hmR : (m : ℝ) = 2 * r + 2 := by rw [hm]; push_cast; ring
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have f1 : (2 : ℝ) ^ (r ^ 2 * f) ≤ b ^ ((r : ℝ) ^ 2 * f) := by
    rw [show ((r : ℝ) ^ 2 * f) = ((r ^ 2 * f : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hb _
  have h8v : 8 * v ≤ b ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h4 : 4 ≤ b ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hb0.le]
  have f2 : (8 * v) ^ (2 * (r + 1) ^ 2 * f) ≤ b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f)) := by
    rw [show (3 * (2 * ((r : ℝ) + 1) ^ 2 * f)) = 3 * ((2 * (r + 1) ^ 2 * f : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_mul_natCast hb0.le]
    exact pow_le_pow_left₀ (by linarith) h8v _
  have hn : 8 * r ≤ 2 ^ (m + 3) := by
    have h1 : r < 2 ^ r := Nat.lt_two_pow_self
    have h2 : 2 ^ r ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add]
    omega
  have h8r : 8 * (r : ℝ) ≤ b ^ ((m : ℝ) + 3) := by
    rw [show ((m : ℝ) + 3) = ((m + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    calc 8 * (r : ℝ) = ((8 * r : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ (m + 3) : ℕ) : ℝ) := by exact_mod_cast hn
    _ = (2 : ℝ) ^ (m + 3) := by push_cast; ring
    _ ≤ b ^ (m + 3) := pow_le_pow_left₀ (by norm_num) hb _
  have h3 : 8 * (r : ℝ) * b ^ (CH * m) ≤ b ^ ((m : ℝ) + 3 + CH * m) := by
    rw [Real.rpow_add hb0]
    exact mul_le_mul_of_nonneg_right h8r (Real.rpow_nonneg hb0.le _)
  have f3 : (8 * (r : ℝ) * b ^ (CH * m)) ^ (80 * r ^ 4 * f)
      ≤ b ^ (((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
    rw [Real.rpow_mul_natCast hb0.le ((m : ℝ) + 3 + CH * m) (80 * r ^ 4 * f)]
    exact pow_le_pow_left₀ (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) h3 _
  have p2 : 0 ≤ (8 * v) ^ (2 * (r + 1) ^ 2 * f) := pow_nonneg (by linarith) _
  have hE := exponent_bound CH C (r : ℝ) (f : ℝ) hCH hC hr1 (Nat.cast_nonneg f)
  calc
    _ ≤ b ^ ((r : ℝ) ^ 2 * f) * b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f))
        * b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f))
        * b ^ (((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
      apply mul_le_mul _ f3 (pow_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) _)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg hb0.le _))
          (Real.rpow_nonneg hb0.le _))
      apply mul_le_mul _ f2 p2 (mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg hb0.le _))
      exact mul_le_mul f1 f2 p2 (Real.rpow_nonneg hb0.le _)
  _ = b ^ ((r : ℝ) ^ 2 * f + 3 * (2 * ((r : ℝ) + 1) ^ 2 * f) + 3 * (2 * ((r : ℝ) + 1) ^ 2 * f)
        + ((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
      rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]
  _ ≤ b ^ (C * (m : ℝ) ^ 2 * f * (C * (r : ℝ) ^ 4)) := by
      apply Real.rpow_le_rpow_of_exponent_le hb1
      rw [hmR]; push_cast; linarith [hE]
  _ = _ := Real.rpow_mul hb0.le _ _

theorem regroup {A B D G Pi H T G' Y U : ℝ} (hA : 0 ≤ A * D) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hG0 : 0 ≤ G) (hPi : 0 ≤ Pi) (hT : 0 ≤ T) (hU : A * D ≤ U) (hY : U * B * B * H ≤ Y)
    (hG : G ≤ G') : A * B * B * D * (G * Pi * H * T) ≤ G' * Pi * Y * T := by
  have hU0 : 0 ≤ U := le_trans hA hU
  have hBBH : 0 ≤ B * B * H := mul_nonneg (mul_nonneg hB hB) hH
  have hGPT : 0 ≤ G * Pi * T := mul_nonneg (mul_nonneg hG0 hPi) hT
  have hY0 : 0 ≤ Y := le_trans (mul_nonneg (mul_nonneg (mul_nonneg hU0 hB) hB) hH) hY
  calc A * B * B * D * (G * Pi * H * T) = (A * D) * (B * B * H) * (G * Pi * T) := by ring
  _ ≤ U * (B * B * H) * (G * Pi * T) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hU hBBH) hGPT
  _ = (U * B * B * H) * (G * Pi * T) := by ring
  _ ≤ Y * (G * Pi * T) := mul_le_mul_of_nonneg_right hY hGPT
  _ ≤ Y * (G' * Pi * T) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG hPi) hT) hY0
  _ = G' * Pi * Y * T := by ring

end GlobalTheory.AmpArith

open GlobalTheory.AmpArith in

theorem GlobalTheory.amplitude_arithmetic : ∀ CH : ℝ, 0 ≤ CH → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ (k r m f j : ℕ) (b v Del S Cs P : ℝ), m = 2 * r + 2 → 1 ≤ j → j ≤ r → r + 2 ≤ k → 1 ≤ f → 2 ≤ b → 1 ≤ v → 2 * v ≤ b → 0 < P → Del = P ^ 2 → 1 ≤ S → (v ^ (k * (r - j) * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)) * (8 * v) ^ (2 * (r + 1) ^ 2 * f) * ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * ((16 * Real.pi * Real.exp 1 / k) ^ (j * (k - 1 - j) * f) * (P ^ (k - 1 - j))⁻¹ * (8 * r * b ^ (CH * m)) ^ (80 * r ^ 4 * f) * S ^ (-(Cs * k))) ≤ (C / k) ^ ((j : ℝ) * ((k : ℝ) - 1 - j) * f) * Del ^ (-(((k : ℝ) - 1 - j) / 2)) * (b ^ (C * (m : ℝ) ^ 2 * f)) ^ (C * (r : ℝ) ^ 4) * S ^ (-(Cs * k)) := by
  intro CH hCH
  refine ⟨100 * (CH + 10), ?_⟩
  intro C hC k r m f j b v Del S Cs P hm hj1 hjr hrk hf hb hv hvb hP hDel hS
  have hv0 : 0 ≤ v := by linarith
  have hb0 : 0 < b := by linarith
  have hr : 1 ≤ r := le_trans hj1 hjr
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hcast : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
    rw [Nat.cast_sub (by omega : j ≤ k - 1), Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hPi : Del ^ (-(((k : ℝ) - 1 - j) / 2)) = (P ^ (k - 1 - j))⁻¹ := by
    rw [hDel, ← Real.rpow_natCast P 2, ← Real.rpow_mul hP.le,
      show ((2 : ℕ) : ℝ) * (-(((k : ℝ) - 1 - j) / 2)) = -(((k - 1 - j : ℕ) : ℝ)) by
        rw [hcast]; push_cast; ring,
      Real.rpow_neg hP.le, Real.rpow_natCast]
  have hG : (16 * Real.pi * Real.exp 1 / k) ^ (j * (k - 1 - j) * f)
      ≤ (C / k) ^ ((j : ℝ) * ((k : ℝ) - 1 - j) * f) := by
    rw [show ((j : ℝ) * ((k : ℝ) - 1 - j) * f) = ((j * (k - 1 - j) * f : ℕ) : ℝ) by
      rw [Nat.cast_mul, Nat.cast_mul, hcast], Real.rpow_natCast]
    apply pow_le_pow_left₀ (by positivity)
    gcongr
    have h1 := Real.pi_lt_d2
    have h2 := Real.exp_one_lt_d9
    have hpe : Real.pi * Real.exp 1 < 3.15 * 2.7182818286 :=
      mul_lt_mul'' h1 h2 Real.pi_pos.le (Real.exp_pos 1).le
    nlinarith
  rw [hPi]
  exact GlobalTheory.AmpArith.regroup
    (mul_nonneg (pow_nonneg hv0 _) (pow_nonneg (mul_nonneg (mul_nonneg
      (Real.rpow_nonneg (by positivity) _) zero_le_one) (by positivity)) _))
    (pow_nonneg (by linarith) _)
    (pow_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) _)
    (pow_nonneg (by positivity) _)
    (inv_nonneg.mpr (pow_nonneg hP.le _))
    (Real.rpow_nonneg (by linarith) _)
    (GlobalTheory.AmpArith.v_part k r f j v hr hv)
    (GlobalTheory.AmpArith.b_part CH C hCH hC r m f b v hm hr hb hv hvb)
    hG
