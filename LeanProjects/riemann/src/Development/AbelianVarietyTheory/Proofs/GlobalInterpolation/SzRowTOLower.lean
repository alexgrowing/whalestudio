import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem factor_products_le_rpow_three_hundred_seventy_seven (x c W Dy k f m d : ℝ) (hx : 1 ≤ x) (hc0 : 0 ≤ c) (hc : c ^ 4 ≤ x)
    (hW0 : 0 ≤ W) (hW : W ^ 4 ≤ x ^ 330) (hD0 : 0 ≤ Dy) (hD : Dy ≤ x ^ 12)
    (hk0 : 0 ≤ k) (hk : k ≤ x ^ 5) (hf0 : 0 ≤ f) (hm : 1 ≤ m) (hkf : k * f / m ≤ x ^ 7)
    (hd : 1 / x ≤ d) :
    (c * W) ^ 4 * Dy ^ 3 * k * f * x / (m * d) ≤ x ^ 377 ∧ Dy * k / m ≤ x ^ 377 := by
  have hx0 : 0 < x := by linarith
  have hm0 : 0 < m := by linarith
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hd' : 1 / d ≤ x := by
    rw [div_le_iff₀ hd0]
    rw [div_le_iff₀ hx0] at hd
    linarith
  refine ⟨?_, ?_⟩
  · calc (c * W) ^ 4 * Dy ^ 3 * k * f * x / (m * d)
        = c ^ 4 * W ^ 4 * Dy ^ 3 * (k * f / m) * x * (1 / d) := by field_simp
      _ ≤ x * x ^ 330 * (x ^ 12) ^ 3 * x ^ 7 * x * x := by gcongr
      _ = x ^ 376 := by ring
      _ ≤ x ^ 377 := pow_le_pow_right₀ hx (by norm_num)
  · calc Dy * k / m ≤ Dy * k := div_le_self (by positivity) hm
      _ ≤ x ^ 12 * x ^ 5 := by gcongr
      _ = x ^ 17 := by ring
      _ ≤ x ^ 377 := pow_le_pow_right₀ hx (by norm_num)

theorem szRow_TO_lower : SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ^ 4 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ C.T.Cp / ((D.R.m : ℝ) * L.de2) ≤ ((TOv L.sc : ℕ) : ℝ)) ∧ (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) * D.R.k / D.R.m ≤ ((TOv L.sc : ℕ) : ℝ))) := by
  intro eps he he' C hC
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  have hCp : C.T.Cp = 1 := hC.2.2.2.2.2.2.2.1
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  have hCP : 1000 ≤ C.T.CP := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 (C.T.CP ^ 4), ?_⟩⟩⟩
  intro D L hLe hx V
  simp only [max_le_iff] at hx
  obtain ⟨hxa, hxP⟩ := hx
  obtain ⟨-, -, hr, hkr, -, -, hL1, -, hZ, hD, hkf, -⟩ := hx1 L.sc D.R hLe hxa V.ranks
  have hxx := L.sc.one_lt_alt
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    exact_mod_cast this
  have hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2 := by
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn]
    exact V.host.2.2.1
  have hT : L.sc.x ^ (377 : ℝ) ≤ ((TOv L.sc : ℕ) : ℝ) := Nat.le_ceil _
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hZ0 : 0 ≤ zBase L := by
    unfold zBase
    have : (0:ℝ) ≤ L.sc.L := by linarith
    positivity
  have hZ' : zBase L ≤ L.sc.x ^ ((687 : ℝ) / 100) := hZ
  set x := L.sc.x with hxdef
  have hx1' : 1 ≤ x := hxx.le
  have hx0 : 0 < x := by linarith
  have cast : ∀ n : ℕ, x ^ ((n : ℕ) : ℝ) = x ^ n := fun n => Real.rpow_natCast x n
  have hPe : zBase L ^ C.T.eP = zBase L ^ (12 : ℕ) := by
    rw [heP]; first | rfl | exact_mod_cast Real.rpow_natCast _ 12
  have hd' : 1 / x ≤ L.de2 := by
    refine le_trans ?_ hd
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx1' (by rw [hLe]; linarith)
  have hW : (zBase L ^ (12 : ℕ)) ^ 4 ≤ x ^ 330 := by
    calc (zBase L ^ (12 : ℕ)) ^ 4 = zBase L ^ 48 := by ring
      _ ≤ (x ^ ((687 : ℝ) / 100)) ^ 48 := by gcongr
      _ = x ^ ((687 : ℝ) / 100 * ((48 : ℕ) : ℝ)) := (Real.rpow_mul_natCast hx0.le _ _).symm
      _ ≤ x ^ ((330 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)
      _ = x ^ 330 := cast 330
  have hk : (D.R.k : ℝ) ≤ x ^ 5 := by
    have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact this.trans (by exact_mod_cast hr)
  have hT' : x ^ 377 ≤ ((TOv L.sc : ℕ) : ℝ) := by exact_mod_cast hT
  obtain ⟨a, b⟩ := factor_products_le_rpow_three_hundred_seventy_seven x C.T.CP (zBase L ^ (12 : ℕ)) ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ)
    D.R.k D.R.f D.R.m L.de2 hx1' (by linarith) hxP (by positivity) hW (Nat.cast_nonneg _)
    (by exact_mod_cast hD) (Nat.cast_nonneg _) hk (Nat.cast_nonneg _) (by linarith)
    (by exact_mod_cast hkf) hd'
  refine ⟨?_, b.trans hT'⟩
  rw [hPe, hCp]
  first
    | (rw [Real.rpow_one]; exact a.trans hT')
    | (rw [pow_one]; exact a.trans hT')

end GlobalTheory.EX
