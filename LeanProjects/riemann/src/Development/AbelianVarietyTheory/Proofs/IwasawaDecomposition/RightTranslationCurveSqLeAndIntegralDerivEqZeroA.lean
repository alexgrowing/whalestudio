import Mathlib

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem integral_intervalIntegral_mul_right_curve {K : Type} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsMulRightInvariant] [IsProbabilityMeasure μ]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E]
    (c : ℝ → K) (hc : Continuous c) (g : K → E) (hg : Continuous g) :
    ∫ x, (∫ t in (0:ℝ)..1, g (x * c t)) ∂μ = ∫ x, g x ∂μ := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hg).isBounded.exists_norm_le
  have hcont : Continuous (Function.uncurry fun (x : K) (t : ℝ) => g (x * c t)) := by
    unfold Function.uncurry
    fun_prop
  have hint : Integrable (Function.uncurry fun (x : K) (t : ℝ) => g (x * c t))
      (μ.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Eventually.of_forall fun p => ?_)
    exact hC _ ⟨_, Set.mem_univ _, rfl⟩
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  rw [integral_integral_swap hint]
  simp_rw [integral_mul_right_eq_self g]
  simp

theorem norm_intervalIntegral_unit_sq_le (h : ℝ → ℂ) (hh : Continuous h) :
    ‖∫ t in (0:ℝ)..1, h t‖ ^ 2 ≤ ∫ t in (0:ℝ)..1, ‖h t‖ ^ 2 := by
  set a : ℝ := ∫ t in (0:ℝ)..1, ‖h t‖ with ha
  have h1 : ‖∫ t in (0:ℝ)..1, h t‖ ≤ a :=
    intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have h2 : 0 ≤ ∫ t in (0:ℝ)..1, (‖h t‖ - a) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
  have hn : Continuous fun t => ‖h t‖ := hh.norm
  have h3 : ∫ t in (0:ℝ)..1, (‖h t‖ - a) ^ 2
      = (∫ t in (0:ℝ)..1, ‖h t‖ ^ 2) - a ^ 2 := by
    have e : ∀ t, (‖h t‖ - a) ^ 2 = (‖h t‖ ^ 2 - 2 * a * ‖h t‖) + a ^ 2 := fun t => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, ← ha]
    · simp; ring
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  have h4 : ‖∫ t in (0:ℝ)..1, h t‖ ^ 2 ≤ a ^ 2 := by
    gcongr
  linarith

theorem right_translation_curve_sq_le_and_integral_deriv_eq_zero :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (c : ℝ → K), Continuous c → c 0 = 1 →
      ∀ f f' : K → ℂ, Continuous f → Continuous f' →
      (∀ x t, HasDerivAt (fun t : ℝ => f (x * c t)) (f' (x * c t)) t) →
      (∫ x, ‖f (x * c 1) - f x‖ ^ 2 ∂μ ≤ ∫ x, ‖f' x‖ ^ 2 ∂μ) ∧ ∫ x, f' x ∂μ = 0 := by
  intro K _ _ _ _ _ _ _ μ _ _ _ c hc h0 f f' hf hf' hd
  have key : ∀ x, f (x * c 1) - f x = ∫ t in (0:ℝ)..1, f' (x * c t) := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd x t)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp [h0]
  have hI : ∀ {E : Type} [NormedAddCommGroup E] [SecondCountableTopology E] (g : K → E),
      Continuous g → Integrable g μ :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  constructor
  · rw [← integral_intervalIntegral_mul_right_curve μ c hc (fun x => ‖f' x‖ ^ 2) (by fun_prop)]
    refine integral_mono (hI _ (by fun_prop)) (hI _ ?_) fun x => ?_
    · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun (x : K) (t : ℝ) => ‖f' (x * c t)‖ ^ 2)
        (by unfold Function.uncurry; fun_prop) 0 1
    · simp only [key]
      exact norm_intervalIntegral_unit_sq_le _ (by fun_prop)
  · rw [← integral_intervalIntegral_mul_right_curve μ c hc f' hf']
    simp_rw [← key]
    rw [integral_sub (hI _ (by fun_prop)) (hI _ hf), integral_mul_right_eq_self f, sub_self]

end GlobalTheory
