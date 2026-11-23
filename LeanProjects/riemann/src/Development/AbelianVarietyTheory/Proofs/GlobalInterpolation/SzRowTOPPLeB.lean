import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem f_mul_r_mul_L_le_pow_fourteen (s : Scale) (R : Ranks) (hx : 2 ≤ s.x) (hR : RankVal s R) :
    (R.f : ℝ) * (R.r : ℝ) * s.L ≤ s.x ^ 14 := by
  have hx1 : 1 ≤ s.x := by linarith
  have hx0 : 0 ≤ s.x := by linarith
  have he0 := s.eps_pos
  have he1 := s.eps_lt
  obtain ⟨⟨-, hn⟩, ⟨-, hm⟩, ⟨-, hk⟩, -⟩ := hR
  have hpow : ∀ (a : ℝ) (n : ℕ), a ≤ n → s.x ^ a ≤ s.x ^ n := fun a n h => by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 h
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ 3 := by
    have h3 := hpow (2 + 8 * s.eps) 3 (by push_cast; linarith)
    have h2 : (R.f : ℝ) = 2 * (R.n : ℝ) := by simp [Ranks.f]
    rw [h2]
    linarith
  have hk5 : (R.k : ℝ) ≤ 2 * s.x ^ 5 := by
    have h5 := hpow (9 / 2 + 10 * s.eps) 5 (by push_cast; linarith)
    linarith
  have hm1 : (R.m : ℝ) ≤ 2 * s.x := by
    have hd : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have hsq : Real.sqrt (s.x * s.delta1) ≤ s.x := by
      calc Real.sqrt (s.x * s.delta1) ≤ Real.sqrt (s.x ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith [mul_le_mul_of_nonneg_left hd hx0]
        _ = s.x := Real.sqrt_sq hx0
    linarith
  have hx5 : s.x ≤ s.x ^ 5 := by
    have h4 : 1 ≤ s.x ^ 4 := one_le_pow₀ hx1
    nlinarith
  have hr : (R.r : ℝ) ≤ 4 * s.x ^ 5 := by
    have h1 : R.r ≤ R.k + R.m := Nat.sub_le _ _
    have h2 : (R.r : ℝ) ≤ R.k + R.m := by exact_mod_cast h1
    linarith
  have hL : s.L ≤ s.x := by
    calc s.x ^ s.eps ≤ s.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = s.x := Real.rpow_one _
  have hL0 : 0 ≤ s.L := Real.rpow_nonneg hx0 _
  have h16 : (16 : ℝ) ≤ s.x ^ 5 := by
    have h1 : (2 : ℝ) ^ 5 ≤ s.x ^ 5 := pow_le_pow_left₀ (by norm_num) hx 5
    norm_num at h1
    linarith
  have hx3 := pow_nonneg hx0 3
  have hx5' := pow_nonneg hx0 5
  calc (R.f : ℝ) * R.r * s.L ≤ (4 * s.x ^ 3) * (4 * s.x ^ 5) * s.x :=
        mul_le_mul (mul_le_mul hf hr (by positivity) (by linarith)) hL hL0
          (mul_nonneg (by linarith) (by linarith))
    _ = 16 * s.x ^ 9 := by ring
    _ ≤ s.x ^ 5 * s.x ^ 9 := mul_le_mul_of_nonneg_right h16 (pow_nonneg hx0 9)
    _ = s.x ^ 14 := by ring

theorem szRow_TO_PP_le_b : SzRow (fun C D L => (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.b ^ (1 / 2 : ℝ)) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ))) := by
  intro eps heps heps' C hC
  obtain ⟨-, -, -, -, -, -, -, -, heP, -, -, -, -, hCP, -, hLast⟩ := hC
  have hCb : 1 ≤ C.T.Cb := hLast C.T.Cb (by simp [FC.cLast])
  obtain ⟨x1, hx1⟩ := GlobalTheory.scale_poly_comparison eps (1259 + C.T.Cb) (1 / 2) heps (by norm_num)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max x1 2) (4 * C.T.CP ^ 3), fun D L hLe hx hV => ?_⟩⟩⟩
  have hxK : 4 * C.T.CP ^ 3 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx2 : 2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxx1 : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1' : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have hCP0 : 0 ≤ C.T.CP := by linarith

  have hXb := (hx1 L.sc hLe hxx1).2.2.1
  have hX' : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx0 _)
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0 _)
  have hxc : L.sc.x ^ (1259 + C.T.Cb) ≤ L.sc.b ^ (1 / 2 : ℝ) :=
    le_trans (le_mul_of_one_le_right (Real.rpow_nonneg hx0 _) hX') hXb
  have hbh : L.sc.b ^ (1 / 2 : ℝ) ≤ L.sc.b := by
    calc L.sc.b ^ (1 / 2 : ℝ) ≤ L.sc.b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
      _ = L.sc.b := Real.rpow_one _

  have hz : zBase L ≤ L.sc.x ^ 14 := f_mul_r_mul_L_le_pow_fourteen L.sc D.R hx2 hV.ranks
  obtain ⟨⟨hn1, -⟩, -, -, -⟩ := hV.ranks
  have hn : 1 ≤ (D.R.n : ℝ) := le_trans (Real.one_le_rpow hx1' (by linarith [L.sc.eps_pos])) hn1
  have hf1 : 1 ≤ (D.R.f : ℝ) := by
    have h2 : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by simp [Ranks.f]
    rw [h2]
    linarith
  have hr1 : 1 ≤ (D.R.r : ℝ) := by
    have h2 := D.R.two_le_m
    have h3 : 1 ≤ D.R.r := by
      unfold Ranks.r
      omega
    exact_mod_cast h3
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow hx1' (le_of_lt L.sc.eps_pos)
  have hz1 : 1 ≤ zBase L := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hL1
  have hz0 : 0 ≤ zBase L := by linarith
  have hz12 : zBase L ^ (12 : ℝ) = zBase L ^ (12 : ℕ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hP1 : 1 ≤ C.T.CP * zBase L ^ (12 : ℝ) := by
    rw [hz12]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hz1)
  have hP2 : C.T.CP * zBase L ^ (12 : ℝ) ≤ C.T.CP * L.sc.x ^ 168 := by
    rw [hz12]
    apply mul_le_mul_of_nonneg_left _ hCP0
    calc zBase L ^ 12 ≤ (L.sc.x ^ 14) ^ 12 := pow_le_pow_left₀ hz0 hz 12
      _ = L.sc.x ^ 168 := by ring
  have hT1 : (1 : ℝ) ≤ ((TOv L.sc : ℕ) : ℝ) := by
    have h1 : 0 < TOv L.sc := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxpos _)
    exact_mod_cast h1
  have hT2 : ((TOv L.sc : ℕ) : ℝ) ≤ 2 * L.sc.x ^ 377 := by
    have h1 : ((TOv L.sc : ℕ) : ℝ) < L.sc.x ^ (377 : ℝ) + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0 _)
    have h2 : L.sc.x ^ (377 : ℝ) = L.sc.x ^ (377 : ℕ) := by
      rw [show (377 : ℝ) = ((377 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3 : 1 ≤ L.sc.x ^ (377 : ℕ) := one_le_pow₀ hx1'
    rw [h2] at h1
    linarith
  have hCb1 : 1 ≤ L.sc.x ^ C.T.Cb := Real.one_le_rpow hx1' (by linarith)
  have hW : (C.T.CP * zBase L ^ (12 : ℝ)) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 * L.sc.x ^ C.T.Cb ≤
      L.sc.x ^ (1259 + C.T.Cb) := by
    have h1 : (C.T.CP * zBase L ^ (12 : ℝ)) ^ 3 ≤ (C.T.CP * L.sc.x ^ 168) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hP2 3
    have h2 : ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ (2 * L.sc.x ^ 377) ^ 2 := pow_le_pow_left₀ (by linarith) hT2 2
    have h3 := mul_le_mul h1 h2 (by positivity) (pow_nonneg (mul_nonneg hCP0 (pow_nonneg hx0 _)) _)
    have h4 : (C.T.CP * L.sc.x ^ 168) ^ 3 * (2 * L.sc.x ^ 377) ^ 2 = 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 := by ring
    have h5 : 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 ≤ L.sc.x ^ 1259 := by
      calc 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 ≤ L.sc.x * L.sc.x ^ 1258 :=
            mul_le_mul_of_nonneg_right hxK (pow_nonneg hx0 _)
        _ = L.sc.x ^ 1259 := by ring
    have h6 : L.sc.x ^ (1259 : ℕ) * L.sc.x ^ C.T.Cb = L.sc.x ^ (1259 + C.T.Cb) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hxpos]
      norm_num
    rw [← h6]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0 _)
    rw [← h4] at h5
    exact le_trans h3 h5
  beta_reduce
  rw [heP]
  generalize ((TOv L.sc : ℕ) : ℝ) = T at hT1 hW ⊢
  generalize C.T.CP * zBase L ^ (12 : ℝ) = P at hP1 hW ⊢
  have hTP : T * P ≤ P ^ 3 * T ^ 2 := by
    have hP3 : P ≤ P ^ 3 := by nlinarith [one_le_pow₀ (n := 2) hP1]
    have hT' : T ≤ T ^ 2 := by nlinarith
    calc T * P ≤ T ^ 2 * P ^ 3 := mul_le_mul hT' hP3 (by linarith) (by positivity)
      _ = P ^ 3 * T ^ 2 := by ring
  have hW' : P ^ 3 * T ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ) := by
    have h1 : P ^ 3 * T ^ 2 ≤ P ^ 3 * T ^ 2 * L.sc.x ^ C.T.Cb :=
      le_mul_of_one_le_right (mul_nonneg (pow_nonneg (by linarith) 3) (sq_nonneg T)) hCb1
    linarith
  have hTPx : T * P * L.sc.x ^ C.T.Cb ≤ P ^ 3 * T ^ 2 * L.sc.x ^ C.T.Cb :=
    mul_le_mul_of_nonneg_right hTP (Real.rpow_nonneg hx0 _)
  refine ⟨?_, ?_, ?_, hW'⟩
  · linarith
  · linarith
  · linarith

end GlobalTheory.EX
