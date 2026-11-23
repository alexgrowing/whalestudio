import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem four_polys_le_of_cube_le (d n r y T : ℝ) (hd0 : 0 ≤ d) (hn0 : 0 ≤ n) (_hr0 : 0 ≤ r)
    (hd : d ≤ y) (hn : n ≤ y) (hr : r ≤ y) (hy : 10000 ≤ y) (hT : y ^ 3 ≤ T) :
    (d + 2) * n + 2 * r ≤ T ∧ 40 * (d + 2) ≤ T ∧ 11 * d ^ 2 ≤ T ∧
      r + 2 * (2 * 5 ^ 4 * r) * (d + 1) ≤ T := by
  have hy0 : 0 ≤ y := by linarith
  have h1 : 10000 * y ≤ y * y := mul_le_mul_of_nonneg_right hy hy0
  have h2 : 10000 * (y * y) ≤ T := by
    have : 10000 * (y * y) ≤ y * (y * y) := mul_le_mul_of_nonneg_right hy (mul_nonneg hy0 hy0)
    have e : y * (y * y) = y ^ 3 := by ring
    linarith
  have hdn : d * n ≤ y * y := mul_le_mul hd hn hn0 hy0
  have hdd : d * d ≤ y * y := mul_le_mul hd hd hd0 hy0
  have hrd : r * d ≤ y * y := mul_le_mul hr hd hd0 hy0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem szRow_rank_polys_le_TO :
    SzRow (fun C D L => (((D.R.f * D.R.r.choose 2 : ℕ) + 2) * (nWv D.R L.sc : ℕ) + 2 * D.R.r ≤ (TOv L.sc : ℕ)) ∧ (40 * ((D.R.f * D.R.r.choose 2 : ℕ) + 2) ≤ (TOv L.sc : ℕ)) ∧ (11 * (D.R.f * D.R.r.choose 2 : ℕ) ^ 2 ≤ (TOv L.sc : ℕ)) ∧ (D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * ((D.R.f * D.R.r.choose 2 : ℕ) + 1) ≤ (TOv L.sc : ℕ))) := by
  intro eps he he' C _
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x0 10000, fun D L heps hx hV => ?_⟩⟩⟩
  obtain ⟨-, -, hr, -, -, -, -, -, -, hD, -, hnW, -⟩ :=
    hx0 L.sc D.R heps (le_trans (le_max_left _ _) hx) hV.ranks
  have hx1 : (10000 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx2 : (1 : ℝ) ≤ L.sc.x := by linarith
  have mono : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le hx2 h
  have hy : (10000 : ℝ) ≤ L.sc.x ^ (23 : ℝ) := by
    have := mono 1 23 (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hT : (L.sc.x ^ (23 : ℝ)) ^ 3 ≤ (TOv L.sc : ℝ) := by
    have e : (L.sc.x ^ (23 : ℝ)) ^ 3 = L.sc.x ^ (69 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rw [e]
    exact le_trans (mono 69 377 (by norm_num)) (Nat.le_ceil _)
  obtain ⟨h1, h2, h3, h4⟩ := four_polys_le_of_cube_le
    ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) (nWv D.R L.sc : ℝ) (D.R.r : ℝ) (L.sc.x ^ (23 : ℝ)) (TOv L.sc : ℝ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (hD.trans (mono _ _ (by norm_num))) (hnW.trans (mono _ _ (by norm_num)))
    (hr.trans (mono _ _ (by norm_num))) hy hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4

end GlobalTheory.EX
