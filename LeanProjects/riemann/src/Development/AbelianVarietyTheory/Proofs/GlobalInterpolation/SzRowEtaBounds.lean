import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparisonStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_eta_bounds : SzRow (fun C D L => (L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3)) ∧ (Real.log L.etaSz ≤ L.sc.x ^ (L.sc.eps / 4)) ∧ ((D.R.t : ℝ) ≤ L.etaSz) ∧ ((D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x) ∧ ((D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD _ => ⟨401, fun ch hch => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps (ch + (1224 : ℕ)) (1 / 2) he0 (by norm_num)
  obtain ⟨x2, h2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) (ch + (3 : ℕ)) 0 1 0 le_rfl
    (by positivity) one_pos
  refine ⟨max (max x1 x2) (max x3 2), fun D L hE hx V => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨-, -, s3, -, -, s6, -⟩ := h1 L.sc hE hx1
  obtain ⟨rf, rm, rr, rk, -, -, -, -, -, -, -, -, -, rt, -⟩ := h2 L.sc D.R hE hx2 V.ranks
  have h3' := h3 L.sc.x hx3
  have heta := V.eta_eq
  have hpos := L.etaSz_pos
  unfold h0v at heta
  push_cast at heta
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hX1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hn1' : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn1
  obtain ⟨s7, -⟩ := s6 D.R.n hn1 (by linarith)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  have rk' : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast rk) rr
  rw [hE]
  generalize L.sc.x = x at *
  generalize L.sc.b = b at *
  generalize L.sc.X' = X at *
  generalize L.sc.w'' D.R.n = w at *
  generalize L.etaSz = η at *
  generalize (D.R.t : ℝ) = t at *
  generalize (D.R.m : ℝ) = m at *
  generalize (D.R.f : ℝ) = f at *
  generalize (D.R.k : ℝ) = k at *
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith
  have hty : t ≤ x ^ ch := rt.trans (Real.rpow_le_rpow_of_exponent_le hx1' hch)
  have e3 : x ^ (ch + (3 : ℕ)) = x ^ ch * x ^ 3 := by rw [Real.rpow_add hx0, Real.rpow_natCast]
  have eB : x ^ (ch + (1224 : ℕ)) = x ^ ch * x ^ 1224 := by rw [Real.rpow_add hx0, Real.rpow_natCast]
  have rf' : f ≤ x ^ 3 := by rw [← Real.rpow_natCast]; exact_mod_cast rf
  have rk'' : k ≤ x ^ 5 := by rw [← Real.rpow_natCast]; exact_mod_cast rk'
  have rt' : t ≤ x ^ 401 := by rw [← Real.rpow_natCast]; exact_mod_cast rt
  have hy1 : 1 ≤ x ^ ch := ht1.trans hty
  have hc1 : x ^ ch ≤ (⌈x ^ ch⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈x ^ ch⌉₊ : ℝ) ≤ x ^ ch + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hup : η ≤ x ^ ch * x ^ 3 := by
    rw [heta]
    have a1 : 2 * (⌈x ^ ch⌉₊ : ℝ) ≤ x ^ ch * x ^ 2 := by
      have : 4 ≤ x ^ 2 := by nlinarith
      nlinarith
    calc m * (2 * (⌈x ^ ch⌉₊ : ℝ)) ≤ x * (x ^ ch * x ^ 2) := by gcongr
      _ = _ := by ring
  have hlo : t ≤ η := by rw [heta]; nlinarith
  have hlog : Real.log η ≤ x ^ (eps / 4) := by
    have a1 : Real.log η ≤ (ch + (3 : ℕ)) * Real.log x := by
      rw [← Real.log_rpow hx0, e3]; exact Real.log_le_log hpos hup
    simp only [zero_mul, add_zero, one_mul] at h3'
    exact a1.trans h3'
  rw [eB] at s3 s7
  generalize x ^ ch = y at *
  have hB0 : 0 ≤ y * x ^ 1224 := by positivity
  have hBb : y * x ^ 1224 ≤ b := by
    have a1 : b ^ (1 / 2 : ℝ) ≤ b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
    rw [Real.rpow_one] at a1
    exact (le_mul_of_one_le_right hB0 hX1).trans (s3.trans a1)
  have hBw : y * x ^ 1224 ≤ w :=
    (le_mul_of_one_le_left hB0 (Real.one_le_rpow hb1 (by norm_num))).trans s7
  have hf0 : 0 < f := by linarith
  refine ⟨?_, hlog, hlo, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    calc η * (t ^ 3 * f * k ^ 3) ≤ (y * x ^ 3) * ((x ^ 401) ^ 3 * x ^ 3 * (x ^ 5) ^ 3) := by gcongr
      _ = y * x ^ 1224 := by ring
      _ ≤ b := hBb
  · rw [le_div_iff₀ hx0]
    calc t * η * x ≤ x ^ 401 * (y * x ^ 3) * x := by gcongr
      _ = y * x ^ 405 := by ring
      _ ≤ y * x ^ 1224 := by gcongr <;> first | assumption | norm_num
      _ ≤ w := hBw
  · have a1 : t + 1 ≤ x * x ^ 401 :=
      calc t + 1 ≤ t + t := by gcongr
        _ = 2 * t := by ring
        _ ≤ x * x ^ 401 := by gcongr
    calc m * (t + 1) * η ≤ x * (x * x ^ 401) * (y * x ^ 3) := by gcongr
      _ = y * x ^ 406 := by ring
      _ ≤ y * x ^ 1224 := by gcongr <;> first | assumption | norm_num
      _ ≤ w := hBw

end GlobalTheory.EX
