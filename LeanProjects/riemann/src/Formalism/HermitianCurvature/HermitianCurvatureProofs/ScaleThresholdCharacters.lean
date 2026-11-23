import Formalism.HermitianCurvature.LowerBlockNormalisedBoundFromComponents

open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.ScaleThresholdCharacters

open Formalism.FourierDecayAlt.PairingProductCorollary

theorem corAProduct_ok : CorAProduct := by
  intro n TT IL y q x P QQ hTT hIL hn hq hqpos hx hP hPr
  have hb : 0 < |P (y + 1)| := abs_pos.mpr hP
  have ha : 0 ≤ |P y| := abs_nonneg _
  have hQ0 : 0 ≤ |QQ (y + 1 / 2)| := abs_nonneg _
  have hexp : Real.exp (4 * n / IL) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by rw [div_le_one hIL]; exact hn)
  have hab : |P y| ≤ Real.exp 1 * |P (y + 1)| := by
    have h1 : |P y| / |P (y + 1)| ≤ Real.exp 1 := by rw [← abs_div]; exact hPr.trans hexp
    rwa [div_le_iff₀ hb] at h1
  have hxa : 0 ≤ |x (y + 1)| := abs_nonneg _
  have hxa2 : |x (y + 1)| ^ 2 ≤ |QQ (y + 1 / 2)| := by
    have := pow_le_pow_left₀ hxa hx 2
    rwa [Real.sq_sqrt hQ0] at this
  have hs0 : 0 ≤ TT ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hTT.le _
  have hs2 : (TT ^ (-(1 / 2 : ℝ))) ^ 2 = TT⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTT.le]
    norm_num
    exact Real.rpow_neg_one TT
  have hu2 : Real.sqrt (|P y * P (y + 1)| / q y) ^ 2 = |P y| * |P (y + 1)| / q y := by
    rw [Real.sq_sqrt (by positivity), abs_mul]
  have he2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  rw [abs_mul]
  have hLn : 0 ≤ |x (y + 1)| * |P y| / q y := by positivity
  have hRn : 0 ≤ Real.exp (1 / 2) * Real.sqrt (|P y * P (y + 1)| / q y) * TT ^ (-(1 / 2 : ℝ)) := by
    positivity
  have hQv : |QQ (y + 1 / 2)| = q y / TT := by rw [hq]; field_simp
  have hsq : (|x (y + 1)| * |P y| / q y) ^ 2 ≤
      (Real.exp (1 / 2) * Real.sqrt (|P y * P (y + 1)| / q y) * TT ^ (-(1 / 2 : ℝ))) ^ 2 := by
    have e1 : (|x (y + 1)| * |P y| / q y) ^ 2 = |x (y + 1)| ^ 2 * |P y| ^ 2 / q y ^ 2 := by ring
    have e2 : (Real.exp (1 / 2) * Real.sqrt (|P y * P (y + 1)| / q y) * TT ^ (-(1 / 2 : ℝ))) ^ 2 =
        Real.exp (1 / 2) ^ 2 * Real.sqrt (|P y * P (y + 1)| / q y) ^ 2 * (TT ^ (-(1 / 2 : ℝ))) ^ 2 := by
      ring
    rw [e1, e2, hu2, hs2, he2]
    calc |x (y + 1)| ^ 2 * |P y| ^ 2 / q y ^ 2 ≤ |QQ (y + 1 / 2)| * |P y| ^ 2 / q y ^ 2 := by gcongr
      _ = |P y| ^ 2 / (TT * q y) := by rw [hQv]; field_simp
      _ ≤ Real.exp 1 * |P (y + 1)| * |P y| / (TT * q y) := by gcongr; nlinarith
      _ = Real.exp 1 * (|P y| * |P (y + 1)| / q y) * TT⁻¹ := by field_simp
  nlinarith

theorem corAConstTop_ok : CorAConstTop := by
  have hRZ : ∀ (Rw ZZ BB TT : ℝ), 0 < TT → 0 ≤ Rw → Rw ≤ Real.exp (1 / 2) → 0 ≤ ZZ →
      ZZ ≤ Real.exp (1 / 2) * BB * TT ^ (-(1 / 2 : ℝ)) →
      Rw * ZZ ≤ Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) := by
    intro Rw ZZ BB TT hTT hR hR' hZ hZ'
    have hp := Real.exp_pos (1 / 2)
    have hBs : 0 ≤ BB * TT ^ (-(1 / 2 : ℝ)) := by
      have h0 : 0 ≤ Real.exp (1 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) := by
        rw [← mul_assoc]; exact hZ.trans hZ'
      exact (mul_nonneg_iff_of_pos_left hp).mp h0
    calc Rw * ZZ ≤ Real.exp (1 / 2) * (Real.exp (1 / 2) * (BB * TT ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul hR' (by rw [← mul_assoc]; exact hZ') hZ hp.le
      _ = Real.exp 1 * (BB * TT ^ (-(1 / 2 : ℝ))) := by rw [← mul_assoc, ← Real.exp_add]; norm_num
      _ ≤ Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) hBs
  refine ⟨?_, ?_⟩
  · intro n ell Rw ZZ BB TT hell hn hTT hR hR' hZ hZ'
    have h := hRZ Rw ZZ BB TT hTT hR hR' hZ hZ'
    calc ((1 / 2) * (4 / ell) ^ n) ^ 2 * Rw * ZZ = (1 / 4) * ((4 / ell) ^ n) ^ 2 * (Rw * ZZ) := by ring
      _ ≤ (1 / 4) * ((4 / ell) ^ n) ^ 2 * (Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Real.exp (3 / 2) * (1 / 4) * (4 / ell) ^ (2 * n) * BB * TT ^ (-(1 / 2 : ℝ)) := by
          rw [show 2 * n = n * 2 by ring, pow_mul]; ring
  · intro Rw ZZ BB TT hTT hR hR' hZ hZ'
    have h := hRZ Rw ZZ BB TT hTT hR hR' hZ hZ'
    linarith [h, show Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) =
      Real.exp (3 / 2) * BB * TT ^ (-(1 / 2 : ℝ)) by ring]

theorem scaleThresholds_ok : ScaleThresholds := by
  intro ka ell sb TT i s r hka hell hTT hi
  have e : ∀ m : ℕ, (4 * ka / ell) ^ m = (4 / ell) ^ m * ka ^ m := fun m => by rw [← mul_pow]; ring
  have key1 : ka ^ ((2 * i : ℤ) - 3) * ka = ka ^ (2 * i - 2) := by
    rw [← zpow_add_one₀ hka.ne', ← zpow_natCast]; congr 1; omega
  have key2 : ka ^ ((2 * i + s : ℤ) - 3) * ka = ka ^ (2 * (i - 1) + s) := by
    rw [← zpow_add_one₀ hka.ne', ← zpow_natCast]; congr 1; omega
  have k3 : (ka ^ (4 * r)) ^ (-(1 / 2 : ℝ)) = (ka ^ (2 * r))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, show 4 * r = 2 * r * 2 by ring, pow_mul,
      Real.sqrt_sq (by positivity)]
  have key3 : ka ^ (2 * (i + r - 1)) * ka = ka ^ (2 * i - 1) * ka ^ (2 * r) := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have hk2 : ka ^ (2 * r) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    linear_combination (Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ (2 * i - 2) * sb) * key1
  · rw [e]
    linear_combination (Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ (2 * (i - 1) + s) * sb) * key2
  · rw [Real.mul_rpow (by positivity) hTT.le, k3]
    have hinv := mul_inv_cancel₀ hk2
    linear_combination (Real.exp (3 / 2) * (1 / 4) * (4 / ell) ^ (2 * (i - 1)) * sb *
      TT ^ (-(1 / 2 : ℝ)) * (ka ^ (2 * r))⁻¹) * key3 +
      (Real.exp (3 / 2) * (1 / 4) * (4 / ell) ^ (2 * (i - 1)) * sb * TT ^ (-(1 / 2 : ℝ)) *
        ka ^ (2 * i - 1)) * hinv

theorem scaleThresholdsOne_ok : ScaleThresholdsOne := by
  intro ka sb TT r hka hTT
  have k3 : (ka ^ (4 * r)) ^ (-(1 / 2 : ℝ)) = (ka ^ (2 * r))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, show 4 * r = 2 * r * 2 by ring, pow_mul,
      Real.sqrt_sq (by positivity)]
  have hk2 : ka ^ (2 * r) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · rw [zpow_neg_one]
    field_simp
  · rw [Real.mul_rpow (by positivity) hTT.le, k3]
    field_simp

theorem scaleThresholdsBelow_ok : ScaleThresholdsBelow := by
  intro ka ell sb TT N IL m i hka hell hN hIL hsb hTT hle
  have h4 : 4 / ell ≤ 28 * N / IL := by
    rw [div_le_div_iff₀ hell hIL]
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 7 * N)).mp hle
    nlinarith
  have hE1 : Real.exp (1 / 4) / 2 ≤ 1 := by
    have h4e : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have hlt := Real.exp_one_lt_d9
    have hpos := Real.exp_pos (1 / 4)
    by_contra hc
    have hc' : 2 < Real.exp (1 / 4) := by linarith [not_le.mp hc]
    have h16 : (2:ℝ) ^ 4 < Real.exp (1 / 4) ^ 4 := pow_lt_pow_left₀ hc' (by norm_num) (by norm_num)
    norm_num at h16
    linarith
  have hE2 : Real.exp (3 / 2) / 4 ≤ 2 := by
    have h2e : Real.exp (3 / 2) ^ 2 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have hlt := Real.exp_one_lt_d9
    have hpos := Real.exp_pos 1
    have hpos' := Real.exp_pos (3 / 2)
    by_contra hc
    have hc' : 8 < Real.exp (3 / 2) := by linarith [not_le.mp hc]
    have h64 : (8:ℝ) ^ 2 < Real.exp (3 / 2) ^ 2 := pow_lt_pow_left₀ hc' (by norm_num) (by norm_num)
    have h3 : Real.exp 1 ^ 3 < 3 ^ 3 := pow_lt_pow_left₀ (by linarith) hpos.le (by norm_num)
    rw [h2e] at h64
    norm_num at h64 h3
    linarith
  refine ⟨?_, ?_⟩
  · have hX : (4 * ka / ell) ^ m ≤ (28 * ka * N / IL) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      rw [show 4 * ka / ell = ka * (4 / ell) by ring, show 28 * ka * N / IL = ka * (28 * N / IL) by ring]
      exact mul_le_mul_of_nonneg_left h4 hka.le
    calc Real.exp (1 / 4) / 2 * sb * (4 * ka / ell) ^ m ≤ Real.exp (1 / 4) / 2 * sb * (28 * ka * N / IL) ^ m :=
          mul_le_mul_of_nonneg_left hX (mul_nonneg (by positivity) hsb)
      _ ≤ 1 * sb * (28 * ka * N / IL) ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE1 hsb) (by positivity)
      _ = sb * (28 * ka * N / IL) ^ m := by ring
  · have hA : (4 / ell) ^ (2 * (i - 1)) ≤ (28 * N / IL) ^ (2 * (i - 1)) :=
      pow_le_pow_left₀ (by positivity) h4 _
    have hC : 0 ≤ sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg hsb (by positivity)) (Real.rpow_nonneg hTT.le _)
    calc Real.exp (3 / 2) / 4 * sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) * (4 / ell) ^ (2 * (i - 1))
        = (Real.exp (3 / 2) / 4) * (sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ))) *
            (4 / ell) ^ (2 * (i - 1)) := by ring
      _ ≤ 2 * (sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ))) * (28 * N / IL) ^ (2 * (i - 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hE2 hC) hA (by positivity) (mul_nonneg (by norm_num) hC)
      _ = 2 * sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) * (28 * N / IL) ^ (2 * (i - 1)) := by ring

theorem scaleCharacter_ok : ScaleCharacter := by
  intro ka i l c hka hi
  have hk : (ka : ℂ) ≠ 0 := by exact_mod_cast hka.ne'
  have he : (3 - 2 * (i : ℤ)) + ((2 * i - 2 : ℕ) : ℤ) = 1 := by omega
  have h1 : (ka : ℂ) ^ (3 - 2 * (i : ℤ)) * (ka : ℂ) ^ (2 * i - 2) = ka := by
    rw [← zpow_natCast, ← zpow_add₀ hk, he, zpow_one]
  have h2 : (ka : ℂ) ^ (3 - 2 * (i : ℤ)) * l * ((ka : ℂ) ^ (2 * i - 2) * c) = (ka : ℂ) * (l * c) := by
    calc (ka : ℂ) ^ (3 - 2 * (i : ℤ)) * l * ((ka : ℂ) ^ (2 * i - 2) * c)
        = ((ka : ℂ) ^ (3 - 2 * (i : ℤ)) * (ka : ℂ) ^ (2 * i - 2)) * (l * c) := by ring
      _ = (ka : ℂ) * (l * c) := by rw [h1]
  rw [h2]
  congr 1
  simp only [map_mul, Complex.conj_ofReal]
  ring

end Formalism.FourierDecayAlt.P.ScaleThresholdCharacters

theorem Formalism.FourierDecayAlt.P.constant_product_corollary : Formalism.FourierDecayAlt.PairingProductCorollary.CorAProduct := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.corAProduct_ok
theorem Formalism.FourierDecayAlt.P.constant_top_corollary : Formalism.FourierDecayAlt.PairingProductCorollary.CorAConstTop := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.corAConstTop_ok
theorem Formalism.FourierDecayAlt.P.scale_thresholds_estimate : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleThresholds := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholds_ok
theorem Formalism.FourierDecayAlt.P.scale_thresholds_at_one : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleThresholdsOne := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholdsOne_ok
theorem Formalism.FourierDecayAlt.P.pairing_product_scale_bounds_below : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleThresholdsBelow := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholdsBelow_ok
theorem Formalism.FourierDecayAlt.P.scale_character_identity : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleCharacter := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleCharacter_ok

end
