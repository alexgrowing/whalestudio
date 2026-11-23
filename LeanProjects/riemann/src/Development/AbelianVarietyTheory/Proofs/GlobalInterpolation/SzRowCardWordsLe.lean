import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem words_real_bound {x e G F m n : ℝ} {k : ℕ} (hx : 1 < x) (he : 0 < e) (hG : 1 ≤ G) (hF : 1 ≤ F)
    (hm0 : 0 ≤ m) (hn0 : 0 ≤ n) (hm : m ≤ 2 * Real.sqrt (x * x ^ (-(e / 8)))) (hn : n ≤ 2 * x ^ (2 + 8 * e))
    (hk : x ^ (9 / 2 + 10 * e) ≤ (k : ℝ)) (hk3 : 3 ≤ k)
    (hK : 2 * (256 * G + F + 2) + 3 ≤ x ^ e) :
    3 * Real.exp (G * m ^ 5 * (2 * n) * x ^ e) ^ 2 * x ^ F ≤ (2 : ℝ) ^ (k - 3) := by
  have hx0 : 0 < x := by linarith
  set y := x ^ (9 / 2 + 9 * e) with hy
  have hxy : x ≤ y := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ y := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hy1 : 1 ≤ y := by linarith
  have hm' : m ≤ 2 * x ^ (1 / 2 : ℝ) := by
    refine hm.trans ?_
    rw [← Real.sqrt_eq_rpow]
    have h1 : x ^ (-(e / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by linarith)
    have : Real.sqrt (x * x ^ (-(e / 8))) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hm5 : m ^ 5 ≤ 32 * x ^ (5 / 2 : ℝ) := by
    have h1 : m ^ 5 ≤ (2 * x ^ (1 / 2 : ℝ)) ^ 5 := pow_le_pow_left₀ hm0 hm' 5
    have h2 : (x ^ (1 / 2 : ℝ)) ^ 5 = x ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [mul_pow, h2] at h1
    linarith
  have hprod : x ^ (5 / 2 : ℝ) * x ^ (2 + 8 * e) * x ^ e = y := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, hy]; congr 1; ring
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hx0 e
  have hA : m ^ 5 * (2 * n) * x ^ e ≤ 128 * y := by
    rw [← hprod]
    have h1 : m ^ 5 * (2 * n) ≤ (32 * x ^ (5 / 2 : ℝ)) * (2 * (2 * x ^ (2 + 8 * e))) :=
      mul_le_mul hm5 (by linarith) (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_right h1 hxe.le
    linarith
  have hky : y * x ^ e ≤ (k : ℝ) := by
    refine le_trans (le_of_eq ?_) hk
    rw [hy, ← Real.rpow_add hx0]; congr 1; ring
  have hlogx : Real.log x ≤ y := by
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hk' : 2 * ((256 * G + F + 2) * y) ≤ ((k - 3 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk3]
    push_cast
    have := mul_le_mul_of_nonneg_left hK (by linarith : (0 : ℝ) ≤ y)
    nlinarith
  have hR : (2 : ℝ) ^ (k - 3) = Real.exp (((k - 3 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hR, Real.rpow_def_of_pos hx0 F, ← Real.exp_nat_mul]
  calc 3 * Real.exp (((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e)) * Real.exp (Real.log x * F)
      ≤ Real.exp 2 * Real.exp (((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e)) * Real.exp (Real.log x * F) := by
        gcongr
    _ = Real.exp (2 + ((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e) + Real.log x * F) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h1 : G * (m ^ 5 * (2 * n) * x ^ e) ≤ G * (128 * y) :=
          mul_le_mul_of_nonneg_left hA (by linarith)
        have h2 : Real.log x * F ≤ y * F := mul_le_mul_of_nonneg_right hlogx (by linarith)
        have h4 : ((k - 3 : ℕ) : ℝ) * (1 / 2) ≤ ((k - 3 : ℕ) : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
        push_cast
        nlinarith

theorem szRow_card_words_le : SzRow (fun C D L => (Fintype.card D.what₂.Word ≤ 2 ^ (D.R.k - 3))) := by
  intro eps he he' C hC
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hP, -, hmid, -⟩ := hC
  have hG : 1 ≤ C.CGam := hmid _ (by simp [FC.cMid])
  have hF : 1 ≤ C.P.CF := hmid _ (by simp [FC.cMid])
  have hG' : 1 ≤ C.CGam * C.P.Cpde := by nlinarith
  have hP0 : 0 < C.P.Cpde := by linarith
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3) ^ eps⁻¹, ?_⟩⟩⟩
  intro D L hLe hx hV
  have hK : 2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3 ≤ L.sc.x ^ eps := by
    have h0 : (0 : ℝ) ≤ 2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3 := by linarith
    have := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hx he.le
    rwa [Real.rpow_inv_rpow h0 he.ne'] at this
  have hn0 := hV.ranks.n_le_of_o hV.host.o_le
  obtain ⟨-, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hV.ranks
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  rw [hV.words, Nat.ceil_le]
  rw [hLe] at hn0 hk
  have hn : (D.R.n : ℝ) / C.P.Cpde ≤ 2 * L.sc.x ^ (2 + 8 * eps) := by
    rw [div_le_iff₀ hP0]; linarith
  simp only [Scale.delta1, hLe] at hm
  have := words_real_bound L.sc.one_lt_alt he hG' hF (Nat.cast_nonneg D.R.m)
    (div_nonneg (Nat.cast_nonneg D.R.n) hP0.le) hm hn hk hk3 hK
  have e : C.CGam * C.P.Cpde * (D.R.m : ℝ) ^ 5 * (2 * ((D.R.n : ℝ) / C.P.Cpde))
      = C.CGam * (D.R.m : ℝ) ^ 5 * (2 * (D.R.n : ℝ)) := by
    field_simp
  rw [e] at this
  simp only [GamL, Scale.L, Ranks.f, hV.CGam_eq, hLe]
  push_cast
  exact this

end GlobalTheory.EX
