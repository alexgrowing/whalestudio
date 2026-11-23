import Mathlib

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

theorem key_bound {X Y M K b : ℝ} {E : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hM : 1 ≤ M) (hK : 0 < K) (hE : 0 < E)
    (hb : 0 ≤ b) (h : X + Y ≤ K * M ^ E) :
    M ^ (-b) ≤ K ^ (b / E) * (X ^ (-(b / (2 * E))) * Y ^ (-(b / (2 * E)))) := by
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  have hs0 : 0 ≤ b / E := div_nonneg hb hE'.le
  have hc : b / (2 * E) = b / E / 2 := by ring
  rw [hc]
  have hXY0 : 0 < X * Y := by nlinarith
  have hsq : Real.sqrt (X * Y) ≤ K * M ^ E := by
    have h1 : Real.sqrt (X * Y) ≤ X + Y := by
      rw [show X + Y = Real.sqrt ((X + Y) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hpow : (X * Y) ^ (b / E / 2) ≤ K ^ (b / E) * M ^ b := by
    rw [show b / E / 2 = (1 / 2) * (b / E) by ring, Real.rpow_mul hXY0.le, ← Real.sqrt_eq_rpow]
    calc Real.sqrt (X * Y) ^ (b / E) ≤ (K * M ^ E) ^ (b / E) :=
          Real.rpow_le_rpow (Real.sqrt_nonneg _) hsq hs0
      _ = K ^ (b / E) * M ^ b := by
        rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul (by linarith)]
        congr 2
        field_simp
  have hA : 0 < (X * Y) ^ (b / E / 2) := Real.rpow_pos_of_pos hXY0 _
  have hM0 : 0 < M ^ b := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith), Real.rpow_neg (by linarith),
    ← mul_inv, ← Real.mul_rpow (by linarith) (by linarith), ← div_eq_mul_inv,
    le_div_iff₀ hA, inv_mul_le_iff₀ hM0]
  linarith

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
