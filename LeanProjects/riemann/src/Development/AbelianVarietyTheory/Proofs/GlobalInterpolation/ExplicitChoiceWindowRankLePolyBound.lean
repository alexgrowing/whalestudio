import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem nWv_le_zBase_pow_four {D : D7} (L : SizeData₂ D) :
    1 ≤ zBase L ∧ (D.R.f : ℝ) * D.R.m ≤ zBase L ∧ ((nWv D.R L.sc : ℕ) : ℝ) ≤ 28 * zBase L ^ 4 := by
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have h2m := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hm : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by omega
    exact_mod_cast this
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by
    have : D.R.m ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by omega
    exact_mod_cast this
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  unfold nWv zBase
  push_cast
  generalize (D.R.f : ℝ) = f at *
  generalize (D.R.r : ℝ) = r at *
  generalize (D.R.m : ℝ) = m at *
  generalize (D.R.k : ℝ) = k at *
  generalize L.sc.L = l at *
  have hfr : 1 ≤ f * r := one_le_mul_of_one_le_of_one_le hf hr
  have hfrZ : f * r ≤ f * r * l := le_mul_of_one_le_right (by positivity) hL
  have hZ : 1 ≤ f * r * l := hfr.trans hfrZ
  refine ⟨hZ, le_trans (by gcongr) hfrZ, ?_⟩
  have hk0 : 0 ≤ k - 1 := by linarith
  have hk3 : (k - 1) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hk0 (by linarith) 3
  have hc := (Nat.ceil_lt_add_one (a := 10 * r * (f + f ^ 2 * (k - 1) ^ 3 * l ^ 2 / m) / 8) (by positivity)).le
  have a1 : f ^ 2 * (k - 1) ^ 3 * l ^ 2 / m ≤ f ^ 2 * r ^ 3 * l ^ 2 := by
    refine (div_le_self (by positivity) hm).trans ?_
    gcongr
  have a2 : 10 * r * (f + f ^ 2 * (k - 1) ^ 3 * l ^ 2 / m) ≤ 10 * r * (f + f ^ 2 * r ^ 3 * l ^ 2) := by gcongr
  have m0 : 1 ≤ (f * r * l) ^ 4 := one_le_pow₀ hZ
  have m1 : f * r * l ≤ (f * r * l) ^ 4 := le_self_pow₀ hZ (by norm_num)
  have m2 : f ^ 2 * r ^ 4 * l ^ 2 ≤ (f * r * l) ^ 4 := by
    have b1 : f ^ 2 ≤ f ^ 4 := pow_le_pow_right₀ hf (by norm_num)
    have b2 : l ^ 2 ≤ l ^ 4 := pow_le_pow_right₀ hL (by norm_num)
    calc f ^ 2 * r ^ 4 * l ^ 2 ≤ f ^ 4 * r ^ 4 * l ^ 4 := by gcongr
      _ = (f * r * l) ^ 4 := by ring
  have e : 10 * r * (f + f ^ 2 * r ^ 3 * l ^ 2) = 10 * (f * r) + 10 * (f ^ 2 * r ^ 4 * l ^ 2) := by ring
  rw [e] at a2
  linarith

theorem szRow_nW_le_PP : SzRow (fun C D L => ((2 * (D.R.f : ℝ) * D.R.m) ^ 4 * ((nWv D.R L.sc : ℕ) : ℝ) ≤ (C.T.CP * zBase L ^ C.T.eP)) ∧ (((nWv D.R L.sc : ℕ) : ℝ) ≤ (C.T.CP * zBase L ^ C.T.eP))) := by
  intro eps _ _ C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ _ => ?_⟩⟩⟩
  obtain ⟨hZ, hfm, hn⟩ := nWv_le_zBase_pow_four L
  obtain ⟨-, -, -, -, -, -, -, -, heP, -, -, -, -, hCP, -⟩ := hC
  have e : zBase L ^ C.T.eP = zBase L ^ (12 : ℕ) := by
    rw [heP, ← Real.rpow_natCast]; norm_num
  have hP : 1000 * zBase L ^ (12 : ℕ) ≤ C.T.CP * zBase L ^ C.T.eP := by
    rw [e]
    exact mul_le_mul_of_nonneg_right hCP (by positivity)
  have h8 : zBase L ^ 8 ≤ zBase L ^ 12 := pow_le_pow_right₀ hZ (by norm_num)
  have h4 : zBase L ^ 4 ≤ zBase L ^ 12 := pow_le_pow_right₀ hZ (by norm_num)
  have h12 : 0 ≤ zBase L ^ 12 := by positivity
  refine ⟨le_trans ?_ hP, le_trans ?_ hP⟩
  · have ha : 2 * (D.R.f : ℝ) * D.R.m ≤ 2 * zBase L := by linarith
    calc (2 * (D.R.f : ℝ) * D.R.m) ^ 4 * ((nWv D.R L.sc : ℕ) : ℝ)
        ≤ (2 * zBase L) ^ 4 * (28 * zBase L ^ 4) := by gcongr
      _ = 448 * zBase L ^ 8 := by ring
      _ ≤ 1000 * zBase L ^ 12 := by linarith
  · linarith

end GlobalTheory.EX
