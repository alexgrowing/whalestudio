import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.IntegralityGoodReduction
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed

open PositivityTheory.RgJS UpperTheory.V.Z.Tf.GOne
open scoped ComplexConjugate

theorem UpperTheory.V.Z.Tf.GOne.logTwo :
    ExtId → LogTwo := by
  intro hE W q X d A hS x
  obtain ⟨F, hFa, hFe⟩ := hE W q X d A hS x x
  simp only [if_true] at hFe
  have hq : ∀ w, (0 : ℝ) < q w := fun w => by exact_mod_cast lt_of_lt_of_le two_pos (hS.primes.two w)
  have hne : ∀ σ : ℝ, 1 < σ → (σ : ℂ) - 1 ≠ 0 := fun σ h => sub_ne_zero.2 (by exact_mod_cast h.ne')
  have h1 : F 1 ≠ 0 := by
    intro h0
    have hc : ContinuousOn (fun t : ℝ => dslope F 1 t) (Set.Icc 1 2) := fun t ht => by
      refine (ContinuousAt.comp (g := dslope F 1) ?_ Complex.continuous_ofReal.continuousAt).continuousWithinAt
      rcases eq_or_ne (t : ℂ) 1 with e | e
      · rw [e]
        exact continuousAt_dslope_same.2 (by simpa using (hFa 1 one_pos).differentiableAt)
      · exact (continuousAt_dslope_of_ne e).2 (hFa t (by linarith [ht.1])).continuousAt
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine dirichlet_series_unbounded landauL newton_identities_low_degree euler_product_log_bound removable_singularity_holds (convergence_of_landau_euler landauL euler_product_log_bound)
      W q X d A hS Unit (fun _ => x) ⟨M, fun σ a b => ?_⟩
    have e1 : ∀ p, lterm q (A x) (A x) σ p = ((DirichletSeriesUnbounded₂.cc A (fun _ : Unit => x) p * Real.exp (-(DirichletSeriesUnbounded₂.ll q p * σ)) : ℝ) : ℂ) :=
      fun p => by simpa using DirichletSeriesUnbounded₂.sum_lterm q A (fun _ : Unit => x) hq σ p
    have e2 := sub_smul_dslope F 1 (σ : ℂ)
    rw [h0, sub_zero, hFe σ a, smul_eq_mul] at e2
    have e3 := hM σ ⟨a.le, b⟩
    simp only [mul_left_cancel₀ (hne σ a) e2, Complex.norm_exp] at e3
    simp only [Finset.univ_unique, Finset.sum_singleton]
    simp only [e1, ← Complex.ofReal_tsum, Complex.ofReal_re] at e3 ⊢
    rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun p => mul_nonneg (DirichletSeriesUnbounded₂.cc_nonneg A _ p) (Real.exp_pos _).le)]
    exact le_trans (by linarith [Real.add_one_le_exp (∑' p, DirichletSeriesUnbounded₂.cc A (fun _ : Unit => x) p * Real.exp (-(DirichletSeriesUnbounded₂.ll q p * σ)))]) e3
  have h2 : ∀ t ∈ Set.Icc (1 : ℝ) 2, F t ≠ 0 := fun t ht => by
    rcases ht.1.eq_or_lt with e | e
    · rw [← e]; simpa using h1
    · rw [hFe t e]; exact mul_ne_zero (hne t e) (Complex.exp_ne_zero _)
  have hc : ContinuousOn (fun t : ℝ => Real.log ‖F t‖) (Set.Icc 1 2) := fun t ht =>
    (((hFa t (by linarith [ht.1])).continuousAt.comp Complex.continuous_ofReal.continuousAt).norm.log
      (norm_ne_zero_iff.2 (h2 t ht))).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun σ a b => ?_⟩
  have h3 := hM σ ⟨a.le, b⟩
  have hn : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hFe σ a, norm_mul, hn, Complex.norm_exp, Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, Real.norm_eq_abs, add_comm] at h3
  exact h3
