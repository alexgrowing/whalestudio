import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.WhittakerHecke.IntegralMaxCompactEqCircleAverage
import Development.AutomorphicArithmetic.WhittakerHecke.CongruenceSubgroupVolumePos
import Development.AutomorphicArithmetic.WhittakerHecke.FiniteIdeleCongruenceVolumePos
import Development.AutomorphicArithmetic.WhittakerHecke.LseriesSummableSqCoeffOfFourLtRe
import Development.AutomorphicArithmetic.WhittakerHecke.LseriesTwistedCoeffEqTsumCoprimeOfSummable
import Development.AutomorphicArithmetic.WhittakerHecke.ZetaIntegralEqZeroOfMemMaximalCompactNotMemLevel
import Development.AutomorphicArithmetic.WhittakerHecke.ZetaIntegralEqLseriesMulGammaMulEvalOfMemLevel
import Development.AutomorphicArithmetic.WhittakerHecke.TwistedZetaIntegralAtCompactEqAtRotation
import Development.AutomorphicArithmetic.WhittakerHecke.HasSumTwistedZetaIntegralDirichletSeries
import Development.AutomorphicArithmetic.WhittakerHecke.MeasurableAndBoundedTwistedZetaIntegralRotation
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerHeckeEigenvaluesAndCoeffEqConvolu

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem rhoB (p : MvPolynomial (Fin 2) ℂ) :
    Measurable (fun t : ℝ => MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p) ∧
      ∃ C : ℝ, ∀ t : ℝ, ‖MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p‖ ≤ C := by
  have hc : Continuous fun x : Fin 2 → ℂ => MvPolynomial.eval x p := MvPolynomial.continuous_eval p
  have hv : Continuous fun t : ℝ => (![(Real.sin t : ℂ), (Real.cos t : ℂ)] : Fin 2 → ℂ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Complex.continuous_ofReal.comp Real.continuous_sin
    · exact Complex.continuous_ofReal.comp Real.continuous_cos
  refine ⟨(hc.comp hv).measurable, ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin 2 → ℂ) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun t => hC _ ?_⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  fin_cases i
  · show ‖((Real.sin t : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real]
    exact Real.abs_sin_le_one t
  · show ‖((Real.cos t : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real]
    exact Real.abs_cos_le_one t

private theorem It_ne {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (s : ℂ) (hs : 4 < s.re) (t : ℝ)
    (h : It D χ φ s t ≠ 0) : ∃ r t : ℝ, r ≠ 0 ∧ Wo D φ (em E (aE (iy r) * rot t)) ≠ 0 := by
  by_contra hn
  push_neg at hn
  refine h ?_
  unfold It
  have : ∀ y : ℝ, Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ 0 * ((|y| : ℝ) : ℂ) ^ (s - 2) = 0 := by
    intro y
    by_cases hy : y = 0
    · subst hy
      have : s - 2 ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0
        simp at this
        linarith
      simp [Complex.zero_cpow this]
    · rw [hn y t hy]
      simp
  simp only [this, integral_zero]

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.fac_of :
    Fac := by
  intro E _ _ _ D P ω χ hCen hU hχω M L N hχ
  by_cases hLN : 0 < L ∧ 0 < N
  swap
  · refine ⟨1, one_ne_zero, fun φ _ hG => ?_⟩
    exact absurd ⟨Nat.pos_of_dvd_of_pos hG.dvd hG.pos, hG.pos⟩ hLN
  obtain ⟨hL, hN⟩ := hLN
  have hcK := UpperTheory.congruenceSubgroup_volume_pos M N hN
  have hcL := UpperTheory.finiteIdele_congruenceVolume_pos L hL
  have hcN := UpperTheory.finiteIdele_congruenceVolume_pos N hN
  have hpi := Real.pi_pos
  refine ⟨((cK M N / (2 * Real.pi) : ℝ) : ℂ) * (cT L : ℂ) * (cT N : ℂ), ?_, ?_⟩
  · have h1 : ((cK M N / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (div_pos hcK (by positivity)).ne'
    have h2 : (cT L : ℂ) ≠ 0 := by exact_mod_cast hcL.ne'
    have h3 : (cT N : ℂ) ≠ 0 := by exact_mod_cast hcN.ne'
    exact mul_ne_zero (mul_ne_zero h1 h2) h3
  intro φ hA hG a hIs e p hp s hs hsum
  obtain ⟨μ, hμ, hco⟩ := UpperTheory.exists_whittaker_hecke_eigenvalues_and_coeff_eq_convolution E D P ω χ hCen hU hχω L N hχ φ hA hG a hIs
  have hY := UpperTheory.has_sum_twisted_zeta_integral_dirichlet_series E D P ω χ hCen hU hχω L N hχ φ hA hG μ hμ s hs
  obtain ⟨hYm, C, hC⟩ := UpperTheory.measurable_and_bounded_twisted_zeta_integral_rotation E D P ω χ hCen hU hχω L N hχ φ hA hG s hs
  obtain ⟨hρm, C', hC'⟩ := rhoB p
  set ρ : ℝ → ℂ := fun t => MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p with hρ
  set Z0 : ℂ := (cT N : ℂ) * LSeries (sqN N) s * ((Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e)) with hZ0
  set G0 : ℂ := (Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e) with hG0
  have e1 : Zu D M χ φ (PhiN N p) s = ∫ k, Yt D χ φ s (gl k) * Zr N p s k ∂M.κ := by
    unfold Zu Yt Zr
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    exact integral_mul_const _ _
  have e2 : ∫ k, Yt D χ φ s (gl k) * Zr N p s k ∂M.κ =
      ((cK M N / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (0 : ℝ)..2 * Real.pi, Yt D χ φ s (rot t) * (Z0 * ρ t) := by
    refine UpperTheory.integral_maxCompact_eq_circle_average M N hN _ (fun t => Yt D χ φ s (rot t) * (Z0 * ρ t)) (hYm.mul (measurable_const.mul hρm))
      ⟨C * (‖Z0‖ * C'), fun t => ?_⟩ (fun k hk hn => ?_) (fun k hk hS t h0 h1 => ?_)
    · rw [norm_mul, norm_mul]
      have h0 : 0 ≤ C := (norm_nonneg _).trans (hC t)
      exact mul_le_mul (hC t) (mul_le_mul_of_nonneg_left (hC' t) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h0
    · show Yt D χ φ s (gl k) * Zr N p s k = 0
      rw [UpperTheory.zeta_integral_eq_zero_of_mem_maximal_compact_not_mem_level N hN p s k hk hn, mul_zero]
    · show Yt D χ φ s (gl k) * Zr N p s k = _
      rw [UpperTheory.zeta_integral_eq_lseries_mul_gamma_mul_eval_of_mem_level N hN e p hp s hs k hk hS t h0 h1,
        UpperTheory.twisted_zeta_integral_at_compact_eq_at_rotation E D P ω χ hCen hU hχω L N hχ φ hA hG s k hk hS t h0 h1]
  have eM : Mk D χ 0 φ p s = ∫ t in (0 : ℝ)..2 * Real.pi, ρ t * It D χ φ s t := rfl
  rw [e1, e2, eM]
  by_cases hI : ∀ t, It D χ φ s t = 0
  · have hY0 : ∀ t, Yt D χ φ s (rot t) = 0 := fun t => by
      have := hY t
      simp only [hI t, mul_zero] at this
      exact this.unique hasSum_zero
    simp [hY0, hI]
  push_neg at hI
  obtain ⟨t₀, ht₀⟩ := hI
  set u : {n : ℕ // 0 < n ∧ n.Coprime N} → ℂ := fun n => μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) with hu
  have hcL' : (cT L : ℂ) ≠ 0 := by exact_mod_cast hcL.ne'
  have hus : Summable u := by
    have h1 := (hY t₀).summable
    have h2 : Summable fun n => u n * ((cT L : ℂ) * It D χ φ s t₀) := by
      refine h1.congr fun n => ?_
      simp only [hu]
      ring
    exact (summable_mul_right_iff (mul_ne_zero hcL' ht₀)).1 h2
  obtain ⟨hbS, hbL⟩ := UpperTheory.lseries_twisted_coeff_eq_tsum_coprime_of_summable N χ μ s hus
  have hYt : ∀ t, Yt D χ φ s (rot t) = (cT L : ℂ) * (∑' n, u n) * It D χ φ s t := fun t => by
    refine (hY t).unique ?_
    have := (hus.hasSum.mul_left (cT L : ℂ)).mul_right (It D χ φ s t)
    exact this
  have hco' := hco (It_ne D χ φ s hs t₀ ht₀)
  have hLs : LSeries a s = (∑' n, u n) * LSeries (sqN N) s := by
    rw [LSeries_congr (fun {n} hn => hco' n hn) s, LSeries_convolution' hbS (UpperTheory.lseries_summable_sq_coeff_of_four_lt_re N s hs), hbL]
  have e3 : ∫ t in (0 : ℝ)..2 * Real.pi, Yt D χ φ s (rot t) * (Z0 * ρ t) =
      ((cT L : ℂ) * (∑' n, u n) * Z0) * ∫ t in (0 : ℝ)..2 * Real.pi, ρ t * It D χ φ s t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show Yt D χ φ s (rot t) * (Z0 * ρ t) = _
    rw [hYt t]
    ring
  rw [e3, hLs, hZ0]
  ring
