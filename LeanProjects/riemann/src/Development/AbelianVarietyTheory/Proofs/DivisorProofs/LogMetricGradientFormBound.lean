import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightProfileDerivFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffDerivBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticDerivBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightProfileDerivBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRadiusDelNormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticParameterBoundsOfDensityStatement

open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.InterpCurv

theorem cutoff_flat {χ : ℝ → ℝ} (hχ : IsCutoff χ) {y : ℝ} (hy0 : 0 < y) (hy2 : y < 2) :
    χ y = 1 ∧ deriv χ y = 0 ∧ deriv (deriv χ) y = 0 := by
  have hev : χ =ᶠ[𝓝 y] fun _ => 1 := by
    filter_upwards [Ioo_mem_nhds hy0 hy2] with x hx
    exact hχ.eq_one x ⟨hx.1.le, hx.2.le⟩
  have hd : deriv χ =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hev.eventually_nhds] with x hx
    have hx' : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := hx
    rw [hx'.deriv_eq, deriv_const]
  exact ⟨hev.self_of_nhds, by rw [hev.deriv_eq, deriv_const], by rw [hd.deriv_eq, deriv_const]⟩

theorem logisticFactor_le {Cμ κ L u : ℝ} (hC : 0 ≤ Cμ) (hκ : 2 * Cμ + 2 < κ) (hL : 0 < L)
    (h2 : 2 * L ≤ u) (hu : 1 ≤ u) :
    logisticFactor κ L u ≤ Real.exp (-Cμ * u) ∧ logisticFactor κ L u ≤ 1 / 2 := by
  have hx : Cμ * u + 1 ≤ κ * (u - L) := by nlinarith
  have h1 : logisticFactor κ L u ≤ Real.exp (-(κ * (u - L))) := by
    rw [logisticFactor, Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos _) (by linarith [Real.exp_pos (κ * (u - L))])
  have h3 : Real.exp (-(κ * (u - L))) ≤ Real.exp (-Cμ * u + -1) :=
    Real.exp_le_exp.2 (by linarith)
  have h4 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
  rw [Real.exp_add] at h3
  have h5 : Real.exp (-Cμ * u) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h6 := Real.exp_pos (-Cμ * u)
  have h7 := Real.exp_pos (-1 : ℝ)
  refine ⟨h1.trans (h3.trans ?_), h1.trans (h3.trans ?_)⟩
  · exact mul_le_of_le_one_right h6.le (h4.trans (by norm_num))
  · calc Real.exp (-Cμ * u) * Real.exp (-1) ≤ 1 * Real.exp (-1) :=
          mul_le_mul_of_nonneg_right h5 h7.le
      _ ≤ 1 / 2 := by rw [one_mul]; exact h4

theorem weightProfile_bounds {Cμ κ : ℝ} {χ : ℝ → ℝ} (hC : 0 ≤ Cμ) (hκ : 2 * Cμ + 2 < κ)
    (hχ : IsCutoff χ) : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ L : ℝ, 1 / 2 ≤ L → ∀ u : ℝ, 1 ≤ u →
      ContDiffAt ℝ 2 (weightProfile χ κ L t) u ∧ 0 ≤ weightProfile χ κ L t u ∧
      weightProfile χ κ L t u < 1 ∧
      |deriv (weightProfile χ κ L t) u| + |deriv (deriv (weightProfile χ κ L t)) u| ≤
        K₁ * (1 - weightProfile χ κ L t u) ∧
      |deriv (weightProfile χ κ L t) u| + |deriv (deriv (weightProfile χ κ L t)) u| ≤
        K₁ * (weightProfile χ κ L t u + Real.exp (-Cμ * u) * (1 - weightProfile χ κ L t u)) ∧
      deriv (weightProfile χ κ L t) u ^ 2 ≤ K₁ * weightProfile χ κ L t u *
        (weightProfile χ κ L t u + Real.exp (-Cμ * u) * (1 - weightProfile χ κ L t u)) := by
  obtain ⟨M, hM, hMb⟩ := GlobalTheory.T.cutoff_deriv_bound χ hχ
  have hκ0 : 0 < κ := by linarith
  refine ⟨(κ + κ ^ 2) + 100 * (M + 1) * (κ + 1) ^ 2, by positivity, ?_⟩
  intro t ht L hL u hu
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have hy0 : 0 < u / L := div_pos hu0 hL0
  obtain ⟨hcd, hd1, hd2⟩ := GlobalTheory.T.weightProfile_deriv_formula χ hχ κ L t u hL0 hu0
  obtain ⟨hσ0, hσ1⟩ := logisticFactor_mem κ L u
  have hc := hχ.mem (u / L) hy0.le
  have hρ := Real.exp_pos (-Cμ * u)
  have hf0 : 0 ≤ t * (χ (u / L) * logisticFactor κ L u) :=
    mul_nonneg ht.1 (mul_nonneg hc.1 hσ0.le)
  have hf1 : t * (χ (u / L) * logisticFactor κ L u) < 1 :=
    calc t * (χ (u / L) * logisticFactor κ L u) ≤ 1 * (1 * logisticFactor κ L u) :=
          mul_le_mul ht.2 (mul_le_mul_of_nonneg_right hc.2 hσ0.le) (mul_nonneg hc.1 hσ0.le)
            zero_le_one
      _ < 1 := by linarith
  have hK1 : 0 ≤ κ + κ ^ 2 := by positivity
  have hK2 : 0 ≤ 100 * (M + 1) * (κ + 1) ^ 2 := by positivity
  rw [hd1, hd2, weightProfile_eq]
  refine ⟨hcd, hf0, hf1, ?_⟩
  rcases lt_or_ge (u / L) 2 with hy2 | hy2
  · obtain ⟨e0, e1, e2⟩ := cutoff_flat hχ hy0 hy2
    obtain ⟨b1, b2, b3⟩ := GlobalTheory.T.logistic_deriv_bounds κ t (logisticFactor κ L u) (Real.exp (-Cμ * u)) hκ0 ht.1 ht.2
      hσ0 hσ1 hρ.le
    simp only [e0, e1, e2, zero_div, zero_mul, zero_add, one_mul, mul_zero, add_zero] at b1 b2 b3 hf0 hf1 ⊢
    have hg : 0 ≤ 1 - t * logisticFactor κ L u := by linarith
    refine ⟨b1.trans ?_, b2.trans ?_, b3.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK2) hg
    · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK2) (add_nonneg hf0 (mul_nonneg hρ.le hg))
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK2)
        hf0) (add_nonneg hf0 (mul_nonneg hρ.le hg))
  · have h2L : 2 * L ≤ u := by linarith [(le_div_iff₀ hL0).1 hy2]
    have hg : 0 ≤ 1 - t * (χ (u / L) * logisticFactor κ L u) := by linarith
    obtain ⟨s1, s2⟩ := logisticFactor_le hC hκ hL0 h2L hu
    obtain ⟨m1, m2, m3⟩ := hMb (u / L) hy0
    obtain ⟨b1, b2, b3⟩ := GlobalTheory.T.weight_profile_deriv_bounds κ M L t (χ (u / L)) (deriv χ (u / L))
      (deriv (deriv χ) (u / L)) (logisticFactor κ L u) (Real.exp (-Cμ * u)) hκ0 hM hL ht.1 ht.2
      hc.1 hc.2 m1 m2 m3 hσ0 s2 s1
    refine ⟨b1.trans ?_, b2.trans ?_, b3.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK1) hg
    · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK1) (add_nonneg hf0 (mul_nonneg hρ.le hg))
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK1)
        hf0) (add_nonneg hf0 (mul_nonneg hρ.le hg))

theorem weightBound_cutWeight : ∀ (Cμ CP κ : ℝ) (χ : ℝ → ℝ), 2 * Cμ + 2 < κ → IsCutoff χ →
    ∃ K : ℝ, ∀ (ι : Type) [Fintype ι] (U : Set (ι → ℂ)) (r : (ι → ℂ) → ℝ)
      (G : (ι → ℂ) → Matrix ι ι ℂ), 0 ≤ Cμ → IsOpen U → ContDiffOn ℝ ∞ r U →
      (∀ z ∈ U, Real.exp 1 ≤ r z) → (∀ z ∈ U, (G z).PosSemidef) →
      (∀ z ∈ U, FormLe (fun ξ η => gradForm r z ξ η / ((r z : ℂ) ^ 2))
        fun ξ η => CP * formOf (G z) ξ η) →
      (∀ z ∈ U, FormAbsLe (ddc (fun x => Real.log (r x)) z) CP (formOf (G z))) →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ R : ℝ, 2 ≤ R →
        WeightBound K Cμ U r (fun z => t * cutWeight χ κ R r z) G := by
  intro Cμ CP κ χ hκ hχ
  by_cases hC : 0 ≤ Cμ
  swap
  · exact ⟨0, fun ι _ U r G hC' => absurd hC' hC⟩
  obtain ⟨K₁, hK₁, hb⟩ := weightProfile_bounds hC hκ hχ
  have hA0 : 0 ≤ 2 * Real.pi * |CP| := by positivity
  refine ⟨K₁ * (2 * Real.pi * |CP| + √(2 * Real.pi * |CP|) + 1), ?_⟩
  intro ι _ U r G _ hU hr hre hG hgrad hddc t ht R hR z hz
  beta_reduce
  have hR0 : 0 < R := by linarith
  have hL : 1 / 2 ≤ Real.log R := by
    have := Real.log_le_log (by norm_num) hR
    linarith [Real.log_two_gt_d9]
  have hrz : 0 < r z := (Real.exp_pos 1).trans_le (hre z hz)
  have hr2 : ContDiffAt ℝ 2 r z := (hr.contDiffAt (hU.mem_nhds hz)).of_le (by norm_cast)
  have hu1 : 1 ≤ Real.log (r z) := by
    rw [Real.le_log_iff_exp_le hrz]; exact hre z hz
  have heq : (fun x => t * cutWeight χ κ R r x) =ᶠ[𝓝 z]
      fun x => weightProfile χ κ (Real.log R) t (Real.log (r x)) := by
    filter_upwards [hr2.continuousAt.eventually (lt_mem_nhds hrz)] with x hx
    rw [cutWeight, weightProfile, Real.rpow_def_of_pos (div_pos hx hR0),
      Real.log_div hx.ne' hR0.ne', mul_comm (Real.log (r x) - Real.log R)]
  obtain ⟨hcd, hf0, hf1, hb1, hb2, hb3⟩ := hb t ht (Real.log R) hL (Real.log (r z)) hu1
  have hsz : t * cutWeight χ κ R r z = weightProfile χ κ (Real.log R) t (Real.log (r z)) :=
    heq.self_of_nhds
  have hlog : ContDiffAt ℝ 2 (fun x => Real.log (r x)) z := hr2.log hrz.ne'
  have hρ : r z ^ (-Cμ) = Real.exp (-Cμ * Real.log (r z)) := by
    rw [Real.rpow_def_of_pos hrz, mul_comm]
  rw [hsz, hρ]
  refine ⟨hf0, hf1.le, fun ξ => Or.inr ⟨hf1, ?_⟩⟩
  have hdel : del (fun x => ((t * cutWeight χ κ R r x : ℝ) : ℂ)) z ξ =
      ((deriv (weightProfile χ κ (Real.log R) t) (Real.log (r z)) : ℝ) : ℂ) *
        del (fun x => ((Real.log (r x) : ℝ) : ℂ)) z ξ := by
    rw [del_congr (f := fun x => ((t * cutWeight χ κ R r x : ℝ) : ℂ))
      (g := fun x => ((weightProfile χ κ (Real.log R) t (Real.log (r x)) : ℝ) : ℂ))
      (heq.mono fun x hx => congrArg Complex.ofReal hx)]
    exact del_ofReal_comp (t := fun x => Real.log (r x)) (h := weightProfile χ κ (Real.log R) t)
      (hcd.differentiableAt two_ne_zero).hasDerivAt (hlog.differentiableAt two_ne_zero) ξ
  have hre2 : (leviForm (fun x => t * cutWeight χ κ R r x) z ξ ξ).re =
      deriv (weightProfile χ κ (Real.log R) t) (Real.log (r z)) *
          (leviForm (fun x => Real.log (r x)) z ξ ξ).re +
        deriv (deriv (weightProfile χ κ (Real.log R) t)) (Real.log (r z)) *
          ‖del (fun x => ((Real.log (r x) : ℝ) : ℂ)) z ξ‖ ^ 2 := by
    rw [leviForm_congr heq,
      leviForm_real_comp (h := weightProfile χ κ (Real.log R) t) (t := fun x => Real.log (r x))
        hcd hlog ξ ξ, dbar_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      Complex.ofReal_re]
  obtain ⟨ha, hl⟩ := GlobalTheory.T.log_radius_del_norm_bound ι r (G z) CP z hr2 hrz (hG z hz) (hgrad z hz) (hddc z hz) ξ
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.T.quadratic_parameter_bounds_of_density K₁ (2 * Real.pi * |CP|) (gnorm (G z) ξ)
    (weightProfile χ κ (Real.log R) t (Real.log (r z)))
    (deriv (weightProfile χ κ (Real.log R) t) (Real.log (r z)))
    (deriv (deriv (weightProfile χ κ (Real.log R) t)) (Real.log (r z)))
    (Real.exp (-Cμ * Real.log (r z))) ‖del (fun x => ((Real.log (r x) : ℝ) : ℂ)) z ξ‖
    (leviForm (fun x => Real.log (r x)) z ξ ξ).re hK₁ hA0 (gnorm_nonneg _ _) hf0 hf1
    (Real.exp_pos _).le (norm_nonneg _) ha hl hb1 hb2 hb3
  rw [hdel, hre2, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact ⟨c1, c2, c3, c4⟩

end GlobalTheory.InterpCurv
