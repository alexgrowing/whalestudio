import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex Filter Topology

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem d4l4_c_pos {r : ℕ} (X : Data E r) (τ : X.Ψ) : 0 < X.c τ := by
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  show 0 < 2 * ‖τ.1 X.ξ0‖
  exact mul_pos two_pos (norm_pos_iff.mpr h)

open Classical in
theorem d4l4_diff_flow {r : ℕ} (X : Data E r) (e : X.Ψ → Fin r → ℂ) (x : Frame X.Ψ r)
    (s : X.Ψ → ℂ) (τ0 : X.Ψ) :
    Differentiable ℂ (fun z : ℂ => X.flowV e (Function.update s τ0 z) x) := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  have hu : Differentiable ℂ (fun z : ℂ => Function.update s τ0 z τ) := by
    by_cases h : τ = τ0
    · subst h
      simpa using differentiable_id
    · simpa [Function.update_of_ne h] using differentiable_const (s τ)
  intro z
  simp only [Data.flowV, Matrix.mul_apply, Data.flowMatV, Matrix.of_apply, mat]
  refine DifferentiableAt.fun_sum fun k _ => ?_
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_mul
  exact hu z

theorem holomorphic_periodicity_extension : HolomorphicPeriodicityExtension (E := E) := by
  classical
  intro r X e he G hG m x hx hreal s hs
  have hdom : ∀ s' : X.Ψ → ℂ, X.flowV e s' x ∈ X.dom ↔ ∀ τ, 0 < 1 + (s' τ).im / X.ttV e x τ :=
    fun s' => (flowDomainCriterion_holds (E := E) r X e he x hx s').1
  set H : (X.Ψ → ℂ) → ℂ := fun s' =>
    G (X.flowV e s' x) - cexp (4 * Real.pi * I * ∑ τ, m τ * s' τ) * G x with hH

  suffices key : ∀ A : Finset X.Ψ, ∀ s' : X.Ψ → ℂ, (∀ τ ∉ A, (s' τ).im = 0) →
      X.flowV e s' x ∈ X.dom → H s' = 0 by
    exact sub_eq_zero.mp (key Finset.univ s (fun τ h => absurd (Finset.mem_univ τ) h) hs)
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro s' hs' _
    have hre : ∀ τ, (((s' τ).re : ℝ) : ℂ) = s' τ := fun τ =>
      Complex.ext (by simp) (by simp [hs' τ (by simp)])
    have h0 := hreal (fun τ => (s' τ).re)
    simp only [hre] at h0
    simp only [hH, h0, sub_self]
  | insert τ0 A hτ0 ih =>
    intro s' hs' hdom'
    have hcond := (hdom s').mp hdom'
    set V : Set ℂ := {z | 0 < 1 + z.im / X.ttV e x τ0} with hVdef
    have hVo : IsOpen V := isOpen_lt continuous_const (by fun_prop)
    have hVc : Convex ℝ V := by
      intro z hz w hw a b ha hb hab
      simp only [hVdef, Set.mem_setOf_eq] at hz hw ⊢
      have him : (a • z + b • w).im = a * z.im + b * w.im := by simp
      have h1 : 1 + (a * z.im + b * w.im) / X.ttV e x τ0 =
          a * (1 + z.im / X.ttV e x τ0) + b * (1 + w.im / X.ttV e x τ0) := by
        linear_combination (-1 : ℝ) * hab
      rw [him, h1]
      rcases ha.lt_or_eq with ha' | ha'
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hz) (mul_nonneg hb hw.le)
      · have hb1 : b = 1 := by linarith
        rw [← ha', hb1]
        simpa using hw
    have hreal0 : ∀ y : ℝ, (y : ℂ) ∈ V := by intro y; simp [hVdef]
    have hmaps : ∀ z ∈ V, X.flowV e (Function.update s' τ0 z) x ∈ X.dom := by
      intro z hz
      rw [hdom]
      intro τ
      by_cases h : τ = τ0
      · subst h
        simpa [hVdef] using hz
      · simpa [Function.update_of_ne h] using hcond τ
    have hu : ∀ τ, Differentiable ℂ (fun z : ℂ => Function.update s' τ0 z τ) := by
      intro τ
      by_cases h : τ = τ0
      · subst h
        simpa using differentiable_id
      · simpa [Function.update_of_ne h] using differentiable_const (s' τ)
    have hdiff : DifferentiableOn ℂ (fun z => H (Function.update s' τ0 z)) V := by
      have h1 : DifferentiableOn ℂ (fun z => G (X.flowV e (Function.update s' τ0 z) x)) V :=
        hG.comp (d4l4_diff_flow X e x s' τ0).differentiableOn (fun z hz => hmaps z hz)
      have hsum : Differentiable ℂ (fun z : ℂ => ∑ τ, m τ * Function.update s' τ0 z τ) := by
        intro z
        exact DifferentiableAt.fun_sum fun τ _ => ((hu τ) z).const_mul (m τ)
      have h2 : Differentiable ℂ (fun z : ℂ =>
          cexp (4 * Real.pi * I * ∑ τ, m τ * Function.update s' τ0 z τ) * G x) :=
        ((hsum.const_mul (4 * Real.pi * I)).cexp).mul_const (G x)
      exact h1.sub h2.differentiableOn
    have han : AnalyticOnNhd ℂ (fun z => H (Function.update s' τ0 z)) V :=
      hdiff.analyticOnNhd hVo

    have hzero_real : ∀ y : ℝ, H (Function.update s' τ0 (y : ℂ)) = 0 := by
      intro y
      apply ih
      · intro τ hτ
        by_cases h : τ = τ0
        · subst h
          simp
        · rw [Function.update_of_ne h]
          exact hs' τ (by simp [h, hτ])
      · exact hmaps _ (hreal0 y)
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), H (Function.update s' τ0 z) = 0 := by
      have ht : Filter.Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
        have h3 := Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
          (s := {(0 : ℝ)}ᶜ) (t := {(0 : ℂ)}ᶜ) (x := 0) (fun y hy => by simpa using hy)
        rwa [Complex.ofReal_zero] at h3
      exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall hzero_real))
    have h0V : (0 : ℂ) ∈ V := by simp [hVdef]
    have hEq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hVc.isPreconnected h0V hfreq
    have h4 := hEq (hcond τ0)
    simpa using h4

end ReciprocityTheory.ChartRestriction.G.FD
