import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_Del_TO_gap : SzRow (fun C D L => ((((TOv L.sc : ℕ) : ℝ)) ^ 2 ≤ ((D.s.Del : ℚ) : ℝ)) ∧ ((((TOv L.sc : ℕ) : ℝ) + (D.R.f * D.R.r.choose 2 : ℕ) + 2) * (((TOv L.sc : ℕ) : ℝ) + (D.R.f * D.R.r.choose 2 : ℕ) + 2 + 2 * (D.R.N D.R.m : ℝ)) ≤ ((D.s.Del : ℚ) : ℝ))) := by
  intro eps he he' C _
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  refine ⟨805, fun cD hcD => ⟨0, fun ch _ => ⟨max x0 35, fun D L hs hx hV => ?_⟩⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hDY, -, -, -, -, hN, -⟩ :=
    hx0 L.sc D.R hs (le_trans (le_max_left _ _) hx) hV.ranks
  have hx35 : (35 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) ≤ L.sc.x := by linarith
  have hxp : (0 : ℝ) < L.sc.x := by linarith
  set y : ℝ := L.sc.x ^ (402 : ℝ) with hy
  have hy1 : (1 : ℝ) ≤ y := Real.one_le_rpow hx1 (by norm_num)
  have h377 : L.sc.x ^ (377 : ℝ) ≤ y := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h12 : L.sc.x ^ (12 : ℝ) ≤ y := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hT : ((TOv L.sc : ℕ) : ℝ) ≤ y + 1 := by
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hxp.le (377 : ℝ))
    unfold TOv
    linarith
  have hDel : 35 * y ^ 2 ≤ ((D.s.Del : ℚ) : ℝ) := by
    rw [hV.Del_eq]
    have h1 : L.sc.x ^ cD ≤ ((Delv L.sc cD : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : L.sc.x ^ (805 : ℝ) ≤ L.sc.x ^ cD := Real.rpow_le_rpow_of_exponent_le hx1 hcD
    have h3 : L.sc.x ^ (805 : ℝ) = L.sc.x * y ^ 2 := by
      rw [hy, show (805 : ℝ) = 1 + (402 + 402) by norm_num, Real.rpow_add hxp, Real.rpow_add hxp,
        Real.rpow_one, sq]
    have h4 : 35 * y ^ 2 ≤ L.sc.x * y ^ 2 := mul_le_mul_of_nonneg_right hx35 (sq_nonneg _)
    rw [Rat.cast_natCast]
    exact h4.trans (h3.symm.le.trans (h2.trans h1))
  have hT0 : (0 : ℝ) ≤ ((TOv L.sc : ℕ) : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · have : ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ (2 * y) ^ 2 := pow_le_pow_left₀ hT0 (by linarith) 2
    nlinarith
  · refine le_trans ?_ hDel
    calc _ ≤ (5 * y) * (7 * y) :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = 35 * y ^ 2 := by ring

end GlobalTheory.EX
