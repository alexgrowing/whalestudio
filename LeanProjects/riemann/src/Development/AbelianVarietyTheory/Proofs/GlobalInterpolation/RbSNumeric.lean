import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rbS_numeric {x E P X b k r m de Del lg : ℝ} (hx : 8 ≤ x) (hE0 : 0 < E) (hE : E ≤ x) (hP : 0 ≤ P)
    (hk0 : 0 ≤ k) (hk : k ≤ 2 * x ^ 5) (hr : r ≤ 2 * k) (hm : 2 ≤ m) (hde : E⁻¹ ≤ de)
    (hD0 : 0 ≤ Del) (hD : Del ≤ 2 * P) (hl0 : 0 ≤ lg) (hl : lg ≤ x) (hb : 0 < b)
    (hX : x ^ 16 ≤ X) (hPb : x ^ 22 * P ≤ b) :
    r * (x * b / X + k * (4 * Del)) * lg * (k * E / (m * de)) ≤ de * m * b := by
  have hx0 : 0 < x := by linarith
  have hxde : x⁻¹ ≤ de := (inv_anti₀ hE0 hE).trans hde
  have hde0 : 0 < de := lt_of_lt_of_le (inv_pos.mpr hx0) hxde
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  have h1 : k * E / (m * de) ≤ 2 * x ^ 7 := by
    calc k * E / (m * de) ≤ (2 * x ^ 5) * x / (1 * x⁻¹) := by
          gcongr
          linarith
      _ = 2 * x ^ 7 := by field_simp
  have h2 : x * b / X ≤ b / (8 * x ^ 14) := by
    calc x * b / X ≤ x * b / x ^ 16 := by gcongr
      _ = b / (x * x ^ 14) := by field_simp
      _ ≤ b / (8 * x ^ 14) := by gcongr
  have h3 : k * (4 * Del) ≤ b / (8 * x ^ 14) := by
    rw [le_div_iff₀ (by positivity)]
    have h128 : (128 : ℝ) ≤ x ^ 3 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 3)
    calc k * (4 * Del) * (8 * x ^ 14) ≤ (2 * x ^ 5) * (4 * (2 * P)) * (8 * x ^ 14) := by gcongr
      _ = 128 * (x ^ 19 * P) := by ring
      _ ≤ x ^ 3 * (x ^ 19 * P) := by gcongr
      _ = x ^ 22 * P := by ring
      _ ≤ b := hPb
  have hr' : r ≤ 4 * x ^ 5 := by linarith
  calc r * (x * b / X + k * (4 * Del)) * lg * (k * E / (m * de))
      ≤ (4 * x ^ 5) * (b / (8 * x ^ 14) + b / (8 * x ^ 14)) * x * (2 * x ^ 7) := by
        gcongr
    _ = x⁻¹ * 2 * b := by field_simp; ring
    _ ≤ de * m * b := by gcongr

theorem szRow_rbS : SzRow (fun C D L => ((D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * lA L ≤
    L.de2 * D.R.m * L.sc.b)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) 16 0 1 0 le_rfl (by linarith) one_pos
  obtain ⟨x2, h2⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 eps (22 + cD) 0 1 0 le_rfl he0 one_pos
  refine ⟨max 8 (max x1 x2), fun D L heps hx V => ?_⟩
  have hx8 : 8 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hx1 := h1 _ (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx)
  have hx2 := h2 _ (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx)
  simp only [zero_mul, add_zero, one_mul] at hx1 hx2
  have hx0 : 0 < L.sc.x := by linarith
  have hone : 1 ≤ L.sc.x := by linarith
  have hP : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hone hcD
  have hn : (0 : ℝ) < D.R.n := by
    unfold Ranks.n
    positivity
  beta_reduce
  unfold lA Scale.b' Scale.a
  rw [L.Sc_eq, V.Del_eq]
  refine rbS_numeric (P := L.sc.x ^ cD) hx8 (Real.rpow_pos_of_pos hx0 _) ?_ (by linarith) (Nat.cast_nonneg _)
    ?_ ?_ ?_ ?_ (by positivity) ?_ (Real.log_nonneg hone) ((Real.log_le_sub_one_of_pos hx0).trans (by linarith))
    (Real.exp_pos _) ?_ ?_
  · calc L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by linarith)
      _ = L.sc.x := Real.rpow_one _
  · refine V.ranks.2.2.1.2.trans ?_
    have : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hone (by push_cast; linarith)
    rw [Real.rpow_natCast] at this
    linarith
  · have h := D.R.m_add_three_le_k
    have : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
    exact_mod_cast this
  · exact_mod_cast D.R.two_le_m
  · rw [L.typeDensity_eq_card_div, le_div_iff₀ hn, ← Real.rpow_neg hx0.le]
    exact V.host.2.2.1
  · have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    simp only [Delv, Rat.cast_natCast]
    linarith
  · unfold Scale.X'
    rw [heps, ← Real.exp_log (pow_pos hx0 16), Real.log_pow]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  · unfold Scale.b Scale.L
    rw [heps, ← Real.rpow_natCast, ← Real.rpow_add hx0, Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)

end GlobalTheory.EX
