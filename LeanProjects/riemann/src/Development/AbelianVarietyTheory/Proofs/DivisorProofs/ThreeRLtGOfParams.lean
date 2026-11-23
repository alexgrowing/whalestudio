import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.BigOn

theorem three_r_lt_g_of_params (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (k : Fin 2) :
    3 * D.R.r < D.host.g k := by
  obtain ⟨Y, hY1, -, -, hY4⟩ := P.g_Y
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb2 : 2 ≤ L.sc.b := by
    unfold Scale.b
    have := Real.add_one_le_exp L.sc.L
    linarith
  have hmk := D.R.m_add_three_le_k
  have hr : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hkb : (2 : ℝ) * D.R.k ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  have hpow : (D.R.k : ℝ) * L.sc.b * ((D.R.k : ℝ) * L.sc.b) ^ 7 = ((D.R.k : ℝ) * L.sc.b) ^ 8 := by ring
  have h7 : (2 : ℝ) ^ 7 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 7 :=
    pow_le_pow_left₀ (by norm_num) (by nlinarith) 7
  have hbig : (6 : ℝ) * D.R.k < ((D.R.k : ℝ) * L.sc.b) ^ 8 := by
    rw [← hpow]
    have : (2 : ℝ) * D.R.k * 2 ^ 7 ≤ (D.R.k : ℝ) * L.sc.b * ((D.R.k : ℝ) * L.sc.b) ^ 7 :=
      mul_le_mul hkb h7 (by norm_num) (by positivity)
    nlinarith
  have hr' : ((3 * D.R.r : ℕ) : ℝ) ≤ 6 * D.R.k := by
    have : 3 * D.R.r ≤ 6 * D.R.k := by omega
    exact_mod_cast this
  have hg : ((3 * D.R.r : ℕ) : ℝ) < (D.host.g k : ℝ) := by
    linarith [(hY4 k).1]
  exact_mod_cast hg

theorem typePrimes_gt_three_r :
    AtPts fun Fm x _ i _ => ∀ k : Fin 2, 3 * (Fm.D x i).R.r < (Fm.D x i).host.g k := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  exact EvPt.of_forall fun x hx i _ _ _ k => three_r_lt_g_of_params _ _ (Fm.params x hx i) k

end GlobalTheory.BigOn
