import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_pp_dim_to_le_rpow :
    SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.x ^ L.Ct) ∧
      (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct) ∧ (((TOv L.sc : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct)) := by
  intro eps h0 h1 C hC
  obtain ⟨xr, hxr⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max xr (max C.T.CP 2), fun D L he hx hV => ?_⟩⟩⟩
  have hx1 : xr ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hx2 : C.T.CP ≤ L.sc.x := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx
  have hx3 : (2 : ℝ) ≤ L.sc.x := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx
  have hone : (1 : ℝ) ≤ L.sc.x := by linarith
  have hpos : (0 : ℝ) < L.sc.x := by linarith
  obtain ⟨-, -, -, -, -, -, -, hZ0, hZ, hD, -⟩ := hxr L.sc D.R he hx1 hV.ranks
  have hCt : L.Ct = 401 := hV.Ct_eq.trans hC.1.2.2.2.2.2.2.2.2.2
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  beta_reduce
  rw [hCt, heP]
  refine ⟨?_, hD.trans (Real.rpow_le_rpow_of_exponent_le hone (by norm_num)), ?_⟩
  · have hz0 : 0 ≤ zBase L := le_trans (Real.rpow_nonneg hpos.le _) hZ0
    have hz : zBase L ^ (12 : ℝ) ≤ L.sc.x ^ ((687 : ℝ) / 100 * 12) := by
      rw [Real.rpow_mul hpos.le]
      exact Real.rpow_le_rpow hz0 hZ (by norm_num)
    calc C.T.CP * zBase L ^ (12 : ℝ) ≤ L.sc.x * L.sc.x ^ ((687 : ℝ) / 100 * 12) :=
          mul_le_mul hx2 hz (Real.rpow_nonneg hz0 _) hpos.le
      _ = L.sc.x ^ (1 + (687 : ℝ) / 100 * 12) := by rw [Real.rpow_add hpos, Real.rpow_one]
      _ ≤ L.sc.x ^ (401 : ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
  · have h377 : (1 : ℝ) ≤ L.sc.x ^ (377 : ℝ) := Real.one_le_rpow hone (by norm_num)
    have hc : ((TOv L.sc : ℕ) : ℝ) < L.sc.x ^ (377 : ℝ) + 1 := Nat.ceil_lt_add_one (by linarith)
    calc ((TOv L.sc : ℕ) : ℝ) ≤ L.sc.x * L.sc.x ^ (377 : ℝ) := by nlinarith
      _ = L.sc.x ^ (1 + 377 : ℝ) := by rw [Real.rpow_add hpos, Real.rpow_one]
      _ ≤ L.sc.x ^ (401 : ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by norm_num)

end GlobalTheory.EX
