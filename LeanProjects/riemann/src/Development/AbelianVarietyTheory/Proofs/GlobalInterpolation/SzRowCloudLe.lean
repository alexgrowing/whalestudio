import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_cloud_le : SzRow (fun C D L => (4 * L.Sc ≤ L.LaG * L.sc.b' / D.R.k) ∧
    (4 * C.P.CDelG * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.LaG * L.sc.b') ∧
    (Real.log (D.s.Del : ℝ) ≤ L.sc.x ^ (L.sc.eps / 4) / 2)) := by
  intro eps he he' C hC
  refine ⟨0, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps (cD + 11) 1 1 0 (by positivity) (by linarith) one_pos
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) cD 1 (1 / 2) 0 le_rfl (by positivity) (by norm_num)
  have hLa : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hCD : 1 ≤ C.P.CDelG := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  refine ⟨max (max x1 x2) (max x3 (128 * C.P.CDelG)), fun D L hε hx hV => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  have hx1' : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hΛ : 1 ≤ L.LaG := by
    rw [hV.La_eq]
    refine le_trans ?_ ((h1 L.sc hε hx1).2.2 C.GK hLa).1
    exact Real.one_le_rpow hx1'.le L.sc.eps_pos.le
  have hp1 : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hx1'.le hcD
  have hDel : (D.s.Del : ℝ) = (⌈L.sc.x ^ cD⌉₊ : ℝ) := by
    rw [hV.Del_eq]; simp [Delv]
  have hD2 : (D.s.Del : ℝ) ≤ 2 * L.sc.x ^ cD := by
    rw [hDel]
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by positivity)
    linarith
  have hD1 : 1 ≤ (D.s.Del : ℝ) := by
    rw [hDel]; exact hp1.trans (Nat.le_ceil _)
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (by positivity) hV.ranks.2.2.1.1
  have hk : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℕ) := by
    refine hV.ranks.2.2.1.2.trans ?_
    have : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hε]; push_cast; linarith)
    rw [Real.rpow_natCast] at this
    linarith
  have hb : L.sc.x ^ cD * L.sc.x ^ (11 : ℕ) ≤ L.sc.b' := by
    have h := h2 L.sc.x hx2
    have e1 : L.sc.x ^ cD * L.sc.x ^ (11 : ℕ) = Real.exp ((cD + 11) * Real.log L.sc.x) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0, Real.rpow_def_of_pos hx0, mul_comm]; norm_num
    have e2 : L.sc.b' = L.sc.x * Real.exp (L.sc.x ^ eps - L.sc.x ^ (eps / 3)) := by
      simp only [Scale.b', Scale.a, Scale.b, Scale.X', Scale.L, hε, Real.exp_sub]; ring
    rw [e1, e2]
    have h5 : Real.exp ((cD + 11) * Real.log L.sc.x) ≤ Real.exp (L.sc.x ^ eps - L.sc.x ^ (eps / 3)) :=
      Real.exp_le_exp.2 (by simp only [pow_zero, mul_one, one_mul] at h; linarith)
    have h6 := Real.exp_pos (L.sc.x ^ eps - L.sc.x ^ (eps / 3))
    nlinarith
  have key : 16 * C.P.CDelG * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.LaG * L.sc.b' := by
    have hk2 : (D.R.k : ℝ) ^ 2 ≤ (2 * L.sc.x ^ (5 : ℕ)) ^ 2 := by gcongr
    have hb0 : 0 ≤ L.sc.b' := le_trans (by positivity) hb
    calc 16 * C.P.CDelG * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)
        ≤ 16 * C.P.CDelG * (2 * L.sc.x ^ (5 : ℕ)) ^ 2 * (2 * L.sc.x ^ cD) := by gcongr
      _ = (128 * C.P.CDelG) * (L.sc.x ^ cD * L.sc.x ^ (10 : ℕ)) := by ring
      _ ≤ L.sc.x * (L.sc.x ^ cD * L.sc.x ^ (10 : ℕ)) := by gcongr
      _ = L.sc.x ^ cD * L.sc.x ^ (11 : ℕ) := by ring
      _ ≤ L.sc.b' := hb
      _ ≤ L.LaG * L.sc.b' := le_mul_of_one_le_left hb0 hΛ
  have hP : 0 ≤ (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hk0, L.Sc_eq]
    nlinarith
  · nlinarith
  · have h := h3 L.sc.x hx3
    simp only [pow_zero, mul_one, Real.rpow_zero] at h
    have h7 : Real.log (D.s.Del : ℝ) ≤ Real.log (2 * L.sc.x ^ cD) := Real.log_le_log (by linarith) hD2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h7
    have h8 := Real.log_two_lt_d9
    rw [hε]
    linarith

end GlobalTheory.EX
