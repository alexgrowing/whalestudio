import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstMulRpowMulLogPowLeRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostBoundsTwoMulRpowLogSqLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bandWidth_le_inv_sq_of_rank_bounds (x e n k d La B c : ℝ) (hx : 1 < x) (hd0 : 0 ≤ d) (hd : d ≤ 1) (hn0 : 0 ≤ n)
    (hn : n ≤ 2 * x ^ (2 + 8 * e)) (hk : x ^ (9 / 2 + 10 * e) ≤ k) (hLa0 : 0 ≤ La)
    (hLa : La ≤ B * Real.log x ^ 2 * (2 * x ^ e))
    (h1 : 64 * B * x ^ (2 + 10 * e) * Real.log x ^ 2 ≤ x ^ (5 / 2 + 10 * e))
    (h2 : 4 * |c| * B * x ^ e * Real.log x ^ 3 ≤ x ^ (5 / 2 + 10 * e)) :
    4 * (2 * n * d) * x ^ e * La / k + c * Real.log x * La / k ≤ x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < k := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hk
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have e1 : x ^ (2 + 10 * e) = x ^ (2 + 8 * e) * x ^ e * x ^ e := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  have e2 : x ^ (5 / 2 + 10 * e) = x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hnd : n * d ≤ 2 * x ^ (2 + 8 * e) := le_trans (mul_le_of_le_one_right hn0 hd) hn
  have t1 : 4 * (2 * n * d) * x ^ e * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc 4 * (2 * n * d) * x ^ e * La = 8 * (n * d) * x ^ e * La := by ring
      _ ≤ 8 * (2 * x ^ (2 + 8 * e)) * x ^ e * (B * Real.log x ^ 2 * (2 * x ^ e)) := by gcongr
      _ = 64 * B * x ^ (2 + 10 * e) * Real.log x ^ 2 / 2 := by rw [e1]; ring
      _ ≤ _ := by linarith
  have t2 : c * Real.log x * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc c * Real.log x * La ≤ |c| * Real.log x * (B * Real.log x ^ 2 * (2 * x ^ e)) := by
          gcongr
          exact le_abs_self c
      _ = 4 * |c| * B * x ^ e * Real.log x ^ 3 / 2 := by ring
      _ ≤ _ := by linarith
  rw [← add_div, div_le_iff₀ hk0]
  have t3 : x ^ (5 / 2 + 10 * e) ≤ x ^ (-2 : ℝ) * k := by
    rw [e2]; gcongr
  linarith

theorem szRow_band_lambda_primes :
    SzRow (fun C D L => G.rhoB D C.GK L.sc ≤ L.sc.x ^ (-2 : ℝ) ∧ L.sc.x ^ L.sc.eps ≤ L.LaG ∧
      (∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L)) ∧ (D.host.pde : ℝ) < L.sc.X' ∧
      (D.host.pde' : ℝ) < L.sc.X' ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) := by
  intro eps he0 he1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hpde, -, hmid, -⟩ := hC
  have hKLa : 1 ≤ C.GK.La := hmid _ (by simp [FC.cMid])
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he0 he1
  obtain ⟨x2, h2⟩ := GlobalTheory.EX.hostBounds eps C.P.Cpde he0 he1 hpde
  obtain ⟨x3, h3⟩ := GlobalTheory.scale_poly_comparison eps 41 1 he0 one_pos
  obtain ⟨x4, h4⟩ := GlobalTheory.scale_poly_comparison eps (2 * C.P.Cpde) 1 he0 one_pos
  obtain ⟨x5, h5⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (2 + 10 * eps) (5 / 2 + 10 * eps)
    (64 * (C.GK.La * CN ^ 2)) 2 (by linarith)
  obtain ⟨x6, h6⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (5 / 2 + 10 * eps)
    (4 * |C.GK.rho * C.GK.CN| * (C.GK.La * CN ^ 2)) 3 (by linarith)
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max (max x5 x6) 512), fun D L he hx hV => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, ⟨hx5, hx6⟩, hx7⟩ := hx
  have hx1' := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  obtain ⟨-, -, hLa⟩ := h1 L.sc he hx1
  obtain ⟨hLa1, hLa2⟩ := hLa C.GK hKLa
  obtain ⟨-, -, -, -, -, -, -, -, hp1, hp2⟩ := h2 L.sc D.R D.host he hx2 hV.ranks hV.host
  obtain ⟨-, -, hb, -⟩ := h3 L.sc he hx3
  obtain ⟨-, -, -, -, -, -, hX⟩ := h4 L.sc he hx4
  have hy0 : 0 < L.sc.x ^ (L.sc.eps / 100) := Real.rpow_pos_of_pos hx0 _
  have hn : (D.R.n : ℝ) / L.sc.x ^ (L.sc.eps / 100) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) := by
    rw [div_le_iff₀ hy0, mul_assoc, ← Real.rpow_add hx0]
    exact hV.ranks.n_le
  have hd : L.sc.delta1 * L.sc.x ^ (L.sc.eps / 100) ≤ 1 := by
    unfold Scale.delta1
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1'.le (by have := L.sc.eps_pos; linarith)
  have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0.le _
  have hnd : 2 * (D.R.n : ℝ) * L.sc.delta1 =
      2 * ((D.R.n : ℝ) / L.sc.x ^ (L.sc.eps / 100)) * (L.sc.delta1 * L.sc.x ^ (L.sc.eps / 100)) := by
    field_simp
  obtain ⟨-, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  obtain ⟨-, hTT, -, -, hg, -⟩ := hV.host
  rw [Real.rpow_one] at hb hX
  have hp : ∀ y : ℝ, Real.log y ≤ 2 * C.P.Cpde * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 → y < L.sc.X' := by
    intro y hy
    have a1 : y ≤ Real.exp (2 * C.P.Cpde * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) :=
      (Real.le_exp_log y).trans (Real.exp_le_exp.2 hy)
    have a2 : 1 < L.sc.x ^ (2 * C.P.Cpde) := Real.one_lt_rpow hx1' (by linarith)
    exact lt_of_le_of_lt a1 (lt_of_lt_of_le (lt_mul_of_one_lt_right (Real.exp_pos _) a2) hX)
  refine ⟨?_, hV.La_eq ▸ hLa1, fun j => ?_, hp _ hp1, hp _ hp2, hTT, ?_⟩
  · unfold G.rhoB G.Nstar
    rw [hnd]
    refine bandWidth_le_inv_sq_of_rank_bounds L.sc.x L.sc.eps _ _ _ _ (C.GK.La * CN ^ 2) _ hx1'
      (mul_nonneg hd0 hy0.le) hd (div_nonneg (Nat.cast_nonneg _) hy0.le) hn hk1
      ((Real.rpow_nonneg hx0.le _).trans hLa1) hLa2 ?_ ?_
    · rw [he]; exact h5 _ hx5
    · rw [he]; exact h6 _ hx6
  · have hk5 : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℝ) := by
      refine hk2.trans ?_
      have : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [he]; linarith)
      linarith
    have hX1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
    have hb0 : 0 < L.sc.b := Real.exp_pos _
    have h41 : L.sc.x ^ (41 : ℕ) ≤ L.sc.b := by
      have : L.sc.x ^ (41 : ℝ) ≤ L.sc.b :=
        (le_mul_of_one_le_right (Real.rpow_nonneg hx0.le _) hX1).trans hb
      exact_mod_cast this
    have hk5' : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℕ) := by exact_mod_cast hk5
    have e9 : Real.exp (9 * L.sc.L) = L.sc.b ^ 9 := by
      unfold Scale.b; rw [← Real.exp_nat_mul]; norm_num
    calc ((D.host.g j : ℕ) : ℝ) ≤ 2 * ((D.R.k : ℝ) * L.sc.b) ^ 8 := (hg j).2
      _ ≤ 2 * ((2 * L.sc.x ^ (5 : ℕ)) * L.sc.b) ^ 8 := by gcongr
      _ = 512 * L.sc.x ^ 40 * L.sc.b ^ 8 := by ring
      _ ≤ L.sc.x * L.sc.x ^ 40 * L.sc.b ^ 8 := by gcongr
      _ = L.sc.x ^ 41 * L.sc.b ^ 8 := by ring
      _ ≤ L.sc.b * L.sc.b ^ 8 := by gcongr
      _ = _ := by rw [e9]; ring
  · unfold ChCode_at
    rw [hV.words]
    exact Nat.le_ceil _

end GlobalTheory.EX
