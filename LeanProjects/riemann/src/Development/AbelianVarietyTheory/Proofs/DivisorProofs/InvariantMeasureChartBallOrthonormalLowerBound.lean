import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfI
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.BallVol

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem spread_zero (X : Data E r) (hr : 0 < r) (τ : X.Ψ) : X.spread (fun _ _ => 0) τ = 0 := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  simp [Data.spread]

theorem nd_le (X : Data E r) : nd X ≤ X.Ψ.card * (r * r) := by
  unfold nd
  rw [Fintype.card_prod, Fintype.card_coe]
  refine Nat.mul_le_mul_left _ ?_
  calc Fintype.card {p : Fin r × Fin r // p.2 < p.1} ≤ Fintype.card (Fin r × Fin r) :=
        Fintype.card_subtype_le _
    _ = r * r := by simp

theorem nat_bound (f r n : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hn : n ≤ f * (r * r)) :
    2 * n * (200 * r ^ 3 * f) + n * n + 1 ≤ 402 * (f * r) ^ 8 := by
  set a := f * r with ha
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hra : r ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_left r (by omega)
  have hfa : f ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_right f (by omega)
  have hna : n ≤ a * a := hn.trans (by rw [ha, ← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hra)
  have h1 : 2 * n * (200 * r ^ 3 * f) ≤ 400 * a ^ 8 := by
    have e : 2 * n * (200 * r ^ 3 * f) ≤ 400 * ((a * a) * (a ^ 3 * a)) := by
      have := Nat.mul_le_mul hna (Nat.mul_le_mul (Nat.pow_le_pow_left hra 3) hfa)
      nlinarith
    refine e.trans (Nat.mul_le_mul_left _ ?_)
    calc a * a * (a ^ 3 * a) = a ^ 6 := by ring
      _ ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by norm_num)
  have h2 : n * n ≤ a ^ 8 := by
    calc n * n ≤ (a * a) * (a * a) := Nat.mul_le_mul hna hna
      _ = a ^ 4 := by ring
      _ ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by norm_num)
  have h3 : 1 ≤ a ^ 8 := Nat.one_le_pow _ _ ha1
  omega

theorem real_bound (f r n : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hn : n ≤ f * (r * r)) :
    Real.exp (-(402 * ((f : ℝ) * r) ^ 8)) ≤ Real.exp (-(1 / 10)) *
      (Real.pi ^ n * (1 / (200 * (r : ℝ) ^ 3 * f)) ^ (2 * n) / n.factorial) := by
  set K : ℝ := 200 * (r : ℝ) ^ 3 * f with hK
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ (r : ℝ) ^ 3 := one_le_pow₀ hr'
    rw [hK]; nlinarith
  have hKpos : 0 < K := by linarith

  have hδ : Real.exp (-K) ≤ 1 / K := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hKpos (by linarith [Real.add_one_le_exp K])
  have hδn : Real.exp (-(2 * n * K)) ≤ (1 / K) ^ (2 * n) := by
    calc Real.exp (-(2 * n * K)) = Real.exp (-K) ^ (2 * n) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      _ ≤ (1 / K) ^ (2 * n) := pow_le_pow_left₀ (Real.exp_pos _).le hδ _
  have hpi : (1 : ℝ) ≤ Real.pi ^ n := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hfac : (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) * n) := by
    have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 : (n : ℝ) ^ n ≤ Real.exp n ^ n :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith [Real.add_one_le_exp (n : ℝ)]) _
    rw [← Real.exp_nat_mul] at h2
    exact h1.trans h2
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hN := nat_bound f r n hf hr hn
  have hNR : 2 * (n : ℝ) * K + n * n + 1 ≤ 402 * ((f : ℝ) * r) ^ 8 := by
    rw [hK]; exact_mod_cast hN
  have hmain : Real.exp (-(402 * ((f : ℝ) * r) ^ 8)) ≤
      Real.exp (-(1 / 10)) * (Real.exp (-(2 * n * K)) / Real.exp ((n : ℝ) * n)) := by
    rw [← Real.exp_sub, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  calc Real.exp (-(2 * n * K)) / Real.exp ((n : ℝ) * n)
      ≤ (1 / K) ^ (2 * n) / n.factorial := div_le_div₀ (by positivity) hδn hfpos hfac
    _ ≤ Real.pi ^ n * (1 / K) ^ (2 * n) / n.factorial := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hpi

theorem ballvol : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r →
    ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
    ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤
      ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))
        (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by
  refine ⟨402, by norm_num, ?_⟩
  intro E _ _ _ r X x hp0 hpr hx
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) hpr
  set la : Wt X.Ψ r := fun _ _ => 0 with hla
  set w : ℝ := ∑ τ, X.spread la τ with hw
  have hw0 : w = 0 := Finset.sum_eq_zero fun τ _ => spread_zero X hr τ
  have hcard : ((X.Ψ.card : ℕ) : ℝ) = fdeg E := by
    rw [← Fintype.card_coe, QuadraticCoefficientForms.card_Psi X]
  have hf1 : (1 : ℝ) ≤ (X.Ψ.card : ℝ) := by rw [hcard]; exact one_le_field_half_degree
  have hf1n : 1 ≤ X.Ψ.card := by exact_mod_cast hf1
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set δ := GlobalTheory.LevGeo.chartRad E r w with hδ
  have hδeq : δ = 1 / (200 * (r : ℝ) ^ 3 * (X.Ψ.card : ℝ)) := by
    rw [hδ, GlobalTheory.LevGeo.chartRad, hw0, zero_add, hcard]
  have hδpos : 0 < δ := by rw [hδeq]; positivity
  have hδle : δ ≤ 1 / (100 * (r : ℝ) ^ 2) := by
    rw [hδeq]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h3 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr1 (by norm_num)
    have h4 : (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 3 * (X.Ψ.card : ℝ) := le_mul_of_one_le_right (by positivity) hf1
    nlinarith
  have hnear : ∀ z : V (nd X), ‖z‖ ≤ δ → cpt X x z ∈ X.dom ∧
      Real.exp (-(1 / 20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1 / 10)) ≤ densF X x z :=
    fun z hz => GlobalTheory.ChartNearOne.chart_near_one E r X la w x hr hx le_rfl z hz
  have hsubO : Metric.ball (0 : V (nd X)) δ ⊆ OmF X x := fun z hz =>
    (hnear z (le_of_lt (mem_ball_zero_iff.1 hz))).1
  have hsub : Metric.ball (0 : V (nd X)) δ ⊆
      Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x := fun z hz =>
    ⟨Metric.ball_subset_ball hδle hz, hsubO hz⟩
  refine le_trans ?_ (measure_mono hsub)
  have hm : muF X x (Metric.ball 0 δ) =
      ∫⁻ z in Metric.ball (0 : V (nd X)) δ, ENNReal.ofReal (densF X x z) := by
    rw [muF, withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      Set.inter_eq_left.2 hsubO]
  rw [hm]
  have hn := nd_le X
  calc ENNReal.ofReal (Real.exp (-(402 * ((X.Ψ.card : ℝ) * r) ^ 8)))
      ≤ ENNReal.ofReal (Real.exp (-(1 / 10))) * volume (Metric.ball (0 : V (nd X)) δ) := by
        rw [GlobalTheory.volume_ball_euclideanSpace_complex 0 hδpos, Fintype.card_fin,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hδeq]
        exact real_bound X.Ψ.card r (nd X) hf1n hr hn
    _ = ∫⁻ z in Metric.ball (0 : V (nd X)) δ, ENNReal.ofReal (Real.exp (-(1 / 10))) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ _ := setLIntegral_mono' measurableSet_ball fun z hz =>
        ENNReal.ofReal_le_ofReal (hnear z (le_of_lt (mem_ball_zero_iff.1 hz))).2.2

end

end GlobalTheory.BallVol
