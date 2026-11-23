import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

open NumberField in
private theorem exists_mul_pow_le_exp_half_rpow (eps K : ℝ) (N : ℕ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → K * x ^ N ≤ Real.exp (x ^ eps / 2) := by
  obtain ⟨x1, hx1⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 eps ((N : ℝ) + 1) 0 (1 / 2) 0 le_rfl heps (by norm_num)
  refine ⟨max (max x1 K) 1, fun x hx => ?_⟩
  have hxK : K ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1' : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  have hlog := hx1 x hx1'
  simp only [zero_mul, add_zero] at hlog
  calc K * x ^ N ≤ x * x ^ N := mul_le_mul_of_nonneg_right hxK (by positivity)
    _ = Real.exp (((N : ℝ) + 1) * Real.log x) := by
        rw [show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul, Real.exp_log hxpos]
        ring
    _ ≤ Real.exp (x ^ eps / 2) := by
        apply Real.exp_le_exp.mpr
        linarith

open NumberField in
private theorem zBase_and_log_b_bounds {D : _root_.Formalism.BasicNotions.D7} (L : _root_.Formalism.BasicNotions.SizeData₂ D) (hR : _root_.GlobalTheory.EX.RankVal L.sc D.R) :
    1 ≤ L.sc.x ∧ (D.R.k : ℝ) ≤ 2 * L.sc.x ^ 5 ∧ (D.R.m : ℝ) ≤ 2 * L.sc.x ^ 5 ∧
      (D.R.f : ℝ) ≤ 2 * L.sc.x ^ 5 ∧ (D.R.r : ℝ) ≤ 4 * L.sc.x ^ 5 ∧
      ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) ≤ 2 * L.sc.x ^ 377 ∧
      Real.log L.sc.b ≤ L.sc.x ∧ 0 ≤ Real.log L.sc.b ∧
      0 ≤ _root_.Formalism.BasicNotions.zBase L ∧ _root_.Formalism.BasicNotions.zBase L ≤ 8 * L.sc.x ^ 11 ∧
      ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ≤ 32 * L.sc.x ^ 15 := by
  obtain ⟨-, -, ⟨-, hk⟩, -⟩ := hR
  set x := L.sc.x with hxdef
  have hx1 : 1 ≤ x := L.sc.one_lt_alt.le
  have hx0 : 0 ≤ x := by linarith
  have heps := L.sc.eps_pos
  have heps' := L.sc.eps_lt
  have hx5 : x ^ (9 / 2 + 10 * L.sc.eps) ≤ x ^ 5 := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    push_cast; linarith
  have hkx : (D.R.k : ℝ) ≤ 2 * x ^ 5 := by linarith
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hrk : D.R.r ≤ 2 * D.R.k := by
    show D.R.k + D.R.m - 1 ≤ 2 * D.R.k
    omega
  have hmx : (D.R.m : ℝ) ≤ 2 * x ^ 5 := le_trans (by exact_mod_cast hmk) hkx
  have hfx : (D.R.f : ℝ) ≤ 2 * x ^ 5 := le_trans (by exact_mod_cast hfk) hkx
  have hrx : (D.R.r : ℝ) ≤ 4 * x ^ 5 := by
    have : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast hrk
    linarith
  have hL0 : 0 ≤ L.sc.L := Real.rpow_nonneg hx0 _
  have hLx : L.sc.L ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show L.sc.eps ≤ 1 by linarith)
    simpa [_root_.Formalism.BasicNotions.Scale.L] using h
  have hlogb : Real.log L.sc.b = L.sc.L := by simp [_root_.Formalism.BasicNotions.Scale.b]
  have hxp : 1 ≤ x ^ 377 := one_le_pow₀ hx1
  have hT : ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) ≤ 2 * x ^ 377 := by
    simp only [_root_.GlobalTheory.EX.TOv]
    have hpow : x ^ (377 : ℝ) = x ^ (377 : ℕ) := by exact_mod_cast Real.rpow_natCast x 377
    rw [hpow]
    have := Nat.ceil_lt_add_one (show 0 ≤ x ^ 377 by positivity)
    linarith
  have hz : _root_.Formalism.BasicNotions.zBase L = (D.R.f : ℝ) * D.R.r * L.sc.L := by simp [_root_.Formalism.BasicNotions.zBase]
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have hch : D.R.r.choose 2 ≤ D.R.r ^ 2 := by
    rw [Nat.choose_two_right]
    calc D.R.r * (D.R.r - 1) / 2 ≤ D.R.r * (D.R.r - 1) := Nat.div_le_self _ _
      _ ≤ D.R.r * D.R.r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = D.R.r ^ 2 := by ring
  have hchR : ((D.R.r.choose 2 : ℕ) : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast hch
  refine ⟨hx1, hkx, hmx, hfx, hrx, hT, by rw [hlogb]; exact hLx, by rw [hlogb]; exact hL0,
    by rw [hz]; positivity, ?_, ?_⟩
  · rw [hz]
    calc (D.R.f : ℝ) * D.R.r * L.sc.L ≤ (2 * x ^ 5) * (4 * x ^ 5) * x := by gcongr
      _ = 8 * x ^ 11 := by ring
  · push_cast
    calc (D.R.f : ℝ) * ((D.R.r.choose 2 : ℕ) : ℝ) ≤ (2 * x ^ 5) * (4 * x ^ 5) ^ 2 := by
          gcongr
          exact le_trans hchR (by gcongr)
      _ = 32 * x ^ 15 := by ring

open NumberField in
private theorem scale_b_rpow_half (s : _root_.Formalism.BasicNotions.Scale) :
    s.b ^ (1 / 2 : ℝ) = Real.exp (s.x ^ s.eps / 2) := by
  simp only [_root_.Formalism.BasicNotions.Scale.b, _root_.Formalism.BasicNotions.Scale.L]
  rw [← Real.exp_mul]
  ring_nf

open NumberField in
private theorem exp_half_le_scale_b (s : _root_.Formalism.BasicNotions.Scale) :
    Real.exp (s.x ^ s.eps / 2) ≤ s.b := by
  simp only [_root_.Formalism.BasicNotions.Scale.b, _root_.Formalism.BasicNotions.Scale.L]
  apply Real.exp_le_exp.mpr
  have : 0 ≤ s.x ^ s.eps := Real.rpow_nonneg (by linarith [s.one_lt_alt]) _
  linarith

open NumberField in

theorem _root_.GlobalTheory.EX.szRow_poly_le_b : _root_.GlobalTheory.EX.SzRow (fun C D L => (((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ (((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b ≤ L.sc.b ^ (1 / 2 : ℝ)) ∧ (C.T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ C.T.eP) ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 ≤ L.sc.b)) := by
  intro eps heps _ C hC
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  have hCP : 1000 ≤ C.T.CP := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x1, h1⟩ := exists_mul_pow_le_exp_half_rpow eps 2048 (377 + 30 + 1 + ⌈C.T.Cb⌉₊) heps
  obtain ⟨x2, h2⟩ := exists_mul_pow_le_exp_half_rpow eps 2048 (377 + 30 + 1) heps
  obtain ⟨x3, h3⟩ := exists_mul_pow_le_exp_half_rpow eps
    (|C.T.CbN| * 16 * C.T.CP ^ 2 * 8 ^ 24 * 32 ^ 3) (15 + 264 + 45) heps
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max x1 x2) x3, fun D L hε hx hL => ?_⟩⟩⟩
  obtain ⟨hx1, hk, hm, hf, hr, hT, hlog, hlog0, hz0, hz, hQ⟩ :=
    zBase_and_log_b_bounds L hL.ranks
  have hxCb : L.sc.x ^ C.T.Cb ≤ L.sc.x ^ ⌈C.T.Cb⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (Nat.le_ceil _)
  have hxCb0 : 0 ≤ L.sc.x ^ C.T.Cb := Real.rpow_nonneg (by linarith) _
  have hb2 : L.sc.b ^ (1 / 2 : ℝ) = Real.exp (L.sc.x ^ eps / 2) := by rw [scale_b_rpow_half, hε]
  have hbb : Real.exp (L.sc.x ^ eps / 2) ≤ L.sc.b := hε ▸ exp_half_le_scale_b L.sc
  have hzP : _root_.Formalism.BasicNotions.zBase L ^ C.T.eP = _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ) := by
    rw [heP]; exact_mod_cast Real.rpow_natCast _ 12
  have hx0 : (0 : ℝ) ≤ L.sc.x := by linarith
  have hxa : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc : x3 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  refine ⟨?_, ?_, ?_⟩
  · calc ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b * L.sc.x ^ C.T.Cb
          ≤ (2 * L.sc.x ^ 377) * (32 * L.sc.x ^ 15) ^ 2 * L.sc.x * L.sc.x ^ ⌈C.T.Cb⌉₊ := by gcongr
      _ = 2048 * L.sc.x ^ (377 + 30 + 1 + ⌈C.T.Cb⌉₊) := by ring
      _ ≤ Real.exp (L.sc.x ^ eps / 2) := h1 _ hxa
      _ ≤ L.sc.b := hbb
  · rw [hb2]
    calc ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b
          ≤ (2 * L.sc.x ^ 377) * (32 * L.sc.x ^ 15) ^ 2 * L.sc.x := by gcongr
      _ = 2048 * L.sc.x ^ (377 + 30 + 1) := by ring
      _ ≤ Real.exp (L.sc.x ^ eps / 2) := h2 _ hxb
  · rw [hzP]
    have hrest : 0 ≤ (D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 *
        ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 := by positivity
    calc C.T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3
          = C.T.CbN * ((D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 *
            ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3) := by ring
      _ ≤ |C.T.CbN| * ((D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 *
            ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3) := mul_le_mul_of_nonneg_right (le_abs_self _) hrest
      _ ≤ |C.T.CbN| * ((4 * L.sc.x ^ 5) * (2 * L.sc.x ^ 5) * (2 * L.sc.x ^ 5) *
            (C.T.CP * (8 * L.sc.x ^ 11) ^ (12 : ℕ)) ^ 2 * (32 * L.sc.x ^ 15) ^ 3) := by gcongr
      _ = (|C.T.CbN| * 16 * C.T.CP ^ 2 * 8 ^ 24 * 32 ^ 3) * L.sc.x ^ (15 + 264 + 45) := by ring
      _ ≤ Real.exp (L.sc.x ^ eps / 2) := h3 _ hxc
      _ ≤ L.sc.b := hbb

end GlobalTheory.EX
