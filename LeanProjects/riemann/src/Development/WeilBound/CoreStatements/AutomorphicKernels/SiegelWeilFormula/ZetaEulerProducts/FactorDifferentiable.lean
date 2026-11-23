import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.MeromorphicAtProd

open Filter Topology Complex NumberField IsDedekindDomain

namespace PositivityTheory.Lord

theorem factor_differentiable (N : ℕ) (hN : N ≠ 0) (c : ℂ) :
    Differentiable ℂ (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) := by
  intro s
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  exact (differentiableAt_const _).sub
    ((differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hN')))

theorem factor_analytic (N : ℕ) (hN : N ≠ 0) (c x : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) x :=
  (PositivityTheory.Lord.factor_differentiable N hN c).analyticAt x

theorem factor_ne_zero (N : ℕ) (hN : 2 ≤ N) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 0 < s.re) :
    1 - c * (N : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hpos : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlt : ‖(N : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hN1 (neg_neg_of_pos hs)
  have h1 : c * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖c * (N : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖c‖ * ‖(N : ℂ) ^ (-s)‖ ≤ 1 * ‖(N : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < 1 := by rwa [one_mul]
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn

theorem factor_ne_zero_int (N : ℕ) (hN : 2 ≤ N) (c : ℂ) (hc : ‖c‖ = 1) (j : ℤ) (hj : j ≠ 0) :
    1 - c * (N : ℂ) ^ (-(j : ℂ)) ≠ 0 := by
  intro h
  have hpos : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have h1 : c * (N : ℂ) ^ (-(j : ℂ)) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖c * (N : ℂ) ^ (-(j : ℂ))‖ = ‖(1 : ℂ)‖ := by rw [h1]
  rw [norm_mul, hc, one_mul, norm_one, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re,
    Complex.intCast_re] at hn
  rcases lt_or_gt_of_ne hj with hj' | hj'
  · have hjr : (j : ℝ) < 0 := by exact_mod_cast hj'
    have : (1 : ℝ) < (N : ℝ) ^ (-(j : ℝ)) := Real.one_lt_rpow hN1 (by linarith)
    linarith
  · have hjr : (0 : ℝ) < j := by exact_mod_cast hj'
    have : (N : ℝ) ^ (-(j : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN1 (by linarith)
    linarith

theorem factor_zo (N : ℕ) (hN : 2 ≤ N) (c : ℂ) (hc : ‖c‖ = 1) (j : ℤ) (hj : j ≠ 0) :
    ZO (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) (j : ℂ) 0 :=
  PositivityTheory.Lord.ZO.of_analytic (PositivityTheory.Lord.factor_analytic N (by omega) c _)
    (PositivityTheory.Lord.factor_ne_zero_int N hN c hc j hj)

theorem factor_zo_zero (N : ℕ) (hN : 2 ≤ N) : ZO (fun s : ℂ => 1 - (N : ℂ) ^ (-s)) 0 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have han : AnalyticAt ℂ (fun s : ℂ => 1 - (N : ℂ) ^ (-s)) 0 := by
    simpa only [one_mul] using PositivityTheory.Lord.factor_analytic N (by omega) 1 0
  have hd : HasDerivAt (fun s : ℂ => 1 - (N : ℂ) ^ (-s))
      (-((N : ℂ) ^ (-(0 : ℂ)) * Complex.log N * (-1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).neg).const_cpow (Or.inl hN')).const_sub 1
  refine PositivityTheory.Lord.ZO.one_of_deriv han ?_ ?_
  · show 1 - (N : ℂ) ^ (-(0 : ℂ)) = 0
    rw [neg_zero, Complex.cpow_zero, sub_self]
  · rw [hd.deriv, neg_zero, Complex.cpow_zero, one_mul, mul_neg_one, neg_neg]
    intro hlog
    have h1 : (N : ℂ) = 1 := by rw [← Complex.exp_log hN', hlog, Complex.exp_zero]
    have : N = 1 := by exact_mod_cast h1
    omega

theorem two_le_absNorm (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact P.isPrime.ne_top
  omega

end PositivityTheory.Lord
