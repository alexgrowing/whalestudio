import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstMulRpowMulLogPowLeRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bandWidth_real_inequality_le_inv_sq {x e n δ k La A c : ℝ} (hx : 1 < x) (hδ : δ ≤ 1)
    (hn : n ≤ 2 * x ^ (2 + 8 * e)) (hn0 : 0 ≤ n) (hk : x ^ (9 / 2 + 10 * e) ≤ k) (hLa0 : 0 ≤ La)
    (hLa : La ≤ A * Real.log x ^ 2 * x ^ e) (hc : 0 ≤ c)
    (h1 : 32 * A * x ^ (2 + 10 * e) * Real.log x ^ 2 ≤ x ^ (5 / 2 + 10 * e))
    (h2 : 2 * c * A * x ^ e * Real.log x ^ 3 ≤ x ^ (5 / 2 + 10 * e)) :
    4 * (2 * n * δ) * x ^ e * La / k + c * Real.log x * La / k ≤ x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hk0 : 0 < k := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hk
  have he0 : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have e1 : x ^ (2 + 10 * e) = x ^ (2 + 8 * e) * x ^ e * x ^ e := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  have e2 : x ^ (5 / 2 + 10 * e) = x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hnδ : n * δ ≤ 2 * x ^ (2 + 8 * e) := (mul_le_of_le_one_right hn0 hδ).trans hn
  have t1 : 4 * (2 * n * δ) * x ^ e * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc 4 * (2 * n * δ) * x ^ e * La = 8 * (n * δ) * x ^ e * La := by ring
      _ ≤ 8 * (2 * x ^ (2 + 8 * e)) * x ^ e * (A * Real.log x ^ 2 * x ^ e) := by
          gcongr
      _ = (32 * A * x ^ (2 + 10 * e) * Real.log x ^ 2) / 2 := by rw [e1]; ring
      _ ≤ _ := by linarith
  have t2 : c * Real.log x * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc c * Real.log x * La ≤ c * Real.log x * (A * Real.log x ^ 2 * x ^ e) := by gcongr
      _ = (2 * c * A * x ^ e * Real.log x ^ 3) / 2 := by ring
      _ ≤ _ := by linarith
  rw [← add_div, div_le_iff₀ hk0]
  have t3 : x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) ≤ x ^ (-2 : ℝ) * k :=
    mul_le_mul_of_nonneg_left hk (Real.rpow_pos_of_pos hx0 _).le
  linarith

theorem szRow_tops_band_bottoms :
    SzRow (fun C D L => ((D.host.TT.card : ℝ) ≤ Nstar L) ∧ (rhoP L C.P.Crho ≤ L.sc.x ^ (-2 : ℝ)) ∧
      (∀ t, (L.bT t : ℝ) ≤ L.sc.b' + Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k)) := by
  intro eps h0 h1 C hC
  have hLa : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hrho : 1 ≤ C.P.Crho := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨CN, x1, hx1⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  obtain ⟨x2, hx2⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (2 + 10 * eps) (5 / 2 + 10 * eps) (32 * (2 * C.GK.La * CN ^ 2)) 2 (by linarith)
  obtain ⟨x3, hx3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (5 / 2 + 10 * eps) (2 * C.P.Crho * (2 * C.GK.La * CN ^ 2)) 3 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 (max x2 x3), fun D L he hx V => ⟨?_, ?_, ?_⟩⟩⟩⟩
  · have := V.host.2.1.2
    unfold LevelStarExponents.Nstar
    linarith
  · have hx1' : x1 ≤ L.sc.x := (le_max_left _ _).trans hx
    have hx2' : x2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
    have hx3' : x3 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
    obtain ⟨-, -, hK⟩ := hx1 L.sc he hx1'
    obtain ⟨hlo, hup⟩ := hK C.GK hLa
    have hxp : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
    have a2 := hx2 _ hx2'
    have a3 := hx3 _ hx3'
    rw [← he] at a2 a3
    unfold rhoP LevelStarExponents.Nstar
    rw [V.La_eq]
    have hδ : L.sc.delta1 ≤ L.sc.x ^ (-(L.sc.eps / 100)) :=
      Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by have := L.sc.eps_pos; linarith)
    have hδ0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hxp.le _
    have hn : (D.R.n : ℝ) * L.sc.delta1 ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) := by
      calc (D.R.n : ℝ) * L.sc.delta1
          ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ (-(L.sc.eps / 100)) :=
            mul_le_mul V.ranks.n_le hδ hδ0 (by positivity)
        _ = _ := by rw [mul_assoc, ← Real.rpow_add hxp]; congr 2; ring
    have key := bandWidth_real_inequality_le_inv_sq (A := 2 * C.GK.La * CN ^ 2) (c := C.P.Crho) L.sc.one_lt_alt (le_refl (1 : ℝ))
      hn (mul_nonneg (Nat.cast_nonneg _) hδ0) V.ranks.2.2.1.1 ((Real.rpow_pos_of_pos hxp _).le.trans hlo)
      (hup.trans (le_of_eq (by ring))) (by linarith) a2 a3
    rw [mul_one, ← mul_assoc 2] at key
    exact key
  · exact V.bT_le

end GlobalTheory.EX
