import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

private theorem exTest (z : ℂ) (v : V) (R : ℝ) :
    ∃ x : L V, ∀ᵐ y : ℝ, y ∈ Set.Icc (-R) R → x y = Complex.exp (z * y) • v := by
  have hc : Continuous fun y : ℝ => Complex.exp (z * y) • v := by fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hc.continuousOn
  have hm : MemLp ((Set.Icc (-R) R).indicator fun y : ℝ => Complex.exp (z * y) • v) 2 volume := by
    rw [memLp_indicator_iff_restrict measurableSet_Icc]
    exact MemLp.of_bound hc.aestronglyMeasurable C (ae_restrict_of_forall_mem measurableSet_Icc hC)
  refine ⟨hm.toLp _, ?_⟩
  filter_upwards [hm.coeFn_toLp] with y hy hm'
  rw [hy, Set.indicator_of_mem hm']

private theorem sumAe (S : Finset ℝ) (c : ℝ → V →L[ℂ] V) (x : L V) :
    ∀ᵐ y : ℝ, (∑ t ∈ S, (c t).compLpL 2 volume (sh V t x) : L V) y = ∑ t ∈ S, c t (x (y + t)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero V 2 (volume : Measure ℝ)] with y hy
    simpa using hy
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [ih, Lp.coeFn_add ((c a).compLpL 2 volume (sh V a x)) (∑ t ∈ S, (c t).compLpL 2 volume (sh V t x) : L V),
      (c a).coeFn_compLpL (sh V a x), sh_ae V a x] with y h1 h2 h3 h4
    rw [h2, Pi.add_apply, h1, h3, h4, Finset.sum_insert ha]

private theorem actTest (u : ℝ →₀ (V →L[ℂ] V)) (κ : ℝ → V →L[ℂ] V) (hk : Ker κ) (z : ℂ) (v : V) :
    ∃ R₀ : ℝ, ∀ R, R₀ ≤ R → ∀ x : L V, (∀ᵐ y : ℝ, y ∈ Set.Icc (-R) R → x y = Complex.exp (z * y) • v) →
      ∀ᵐ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
        ((u.sum fun t c => c.compLpL 2 volume (sh V t x)) + conv κ x : L V) y =
          Complex.exp (z * y) • ((u.sum fun t c => Complex.exp (z * t) • c) + symb κ z) v := by
  obtain ⟨r, hr⟩ := (u.support.finite_toSet.isCompact.union hk.2.isCompact).isBounded.subset_closedBall (0 : ℝ)
  refine ⟨r + 1, fun R hR x hx => ?_⟩
  have hmem : ∀ t ∈ (u.support : Set ℝ) ∪ tsupport κ, ∀ y ∈ Set.Icc (0 : ℝ) 1, y + t ∈ Set.Icc (-R) R := by
    intro t ht y hy
    have := hr ht
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le] at this
    constructor <;> linarith [this.1, this.2, hy.1, hy.2]
  have hs : ∀ᵐ y : ℝ, ∀ t ∈ u.support, y + t ∈ Set.Icc (-R) R → x (y + t) = Complex.exp (z * (y + t : ℝ)) • v := by
    rw [Filter.eventually_all_finset]
    intro t _
    exact (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hx
  have hint : Integrable fun t : ℝ => Complex.exp (z * t) • κ t := by
    have h1 : Continuous fun t : ℝ => Complex.exp (z * t) := by fun_prop
    exact (h1.smul hk.1).integrable_of_hasCompactSupport (hk.2.smul_left (f := fun t : ℝ => Complex.exp (z * t)))
  filter_upwards [hs, sumAe u.support u x, (convSpec κ hk x).1,
    Lp.coeFn_add (u.sum fun t c => c.compLpL 2 volume (sh V t x) : L V) (conv κ x)] with y h1 h2 h3 h4 hy
  rw [h4, Pi.add_apply, h3, ContinuousLinearMap.add_apply, smul_add]
  congr 1
  · rw [Finsupp.sum, h2, Finsupp.sum, ContinuousLinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [h1 t ht (hmem t (Or.inl ht) y hy), map_smul, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.exp_add]
    push_cast
    rw [mul_add]
  · rw [symb, ContinuousLinearMap.integral_apply hint, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_add_left volume y).quasiMeasurePreserving.ae hx] with t ht
    by_cases h : t ∈ tsupport κ
    · rw [ht (hmem t (Or.inr h) y hy), map_smul, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.exp_add]
      push_cast
      rw [mul_add]
    · simp [image_eq_zero_of_notMem_tsupport h]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.actUniq :
    ∀ {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V →ₗᵢ[ℂ] H) (Y : H →L[ℂ] H) (s s' : ℂ → V →L[ℂ] V), Act J Y s → Act J Y s' → s = s' := by
  rintro H V _ _ _ _ _ _ _ J Y s s' ⟨u, κ, hk, hY, hs⟩ ⟨u', κ', hk', hY', hs'⟩
  funext z
  ext1 v
  obtain ⟨R, hR⟩ := actTest u κ hk z v
  obtain ⟨R', hR'⟩ := actTest u' κ' hk' z v
  obtain ⟨x, hx⟩ := exTest z v (max R R')
  have e := J.injective ((hY x).symm.trans (hY' x))
  have h1 := hR _ (le_max_left R R') x hx
  have h2 := hR' _ (le_max_right R R') x hx
  rw [← hs] at h1
  rw [← hs', ← e] at h2
  by_contra hne
  have h3 : ∀ᵐ y : ℝ, y ∉ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [h1, h2] with y a b hy
    exact hne (smul_right_injective V (Complex.exp_ne_zero (z * y)) ((a hy).symm.trans (b hy)))
  have h4 : volume (Set.Icc (0 : ℝ) 1) = 0 := measure_eq_zero_iff_ae_notMem.2 h3
  simp at h4
