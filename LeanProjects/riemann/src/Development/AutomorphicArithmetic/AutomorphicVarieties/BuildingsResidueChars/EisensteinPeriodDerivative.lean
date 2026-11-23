import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv

open UpperTheory.V.Sd.Eis

private theorem UpperTheory.exists_bound_of_continuous_periodic_cocompact (A : Type) [AddCommGroup A] [TopologicalSpace A] (Γ : AddSubgroup A)
    (hC : Cocpt Γ) (g : A → ℝ → ℂ) (hg : Continuous (Function.uncurry g))
    (hgp : ∀ γ ∈ Γ, ∀ (x : A), g (γ + x) = g x) :
    ∃ M : ℝ, ∀ x : A, ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖g x t‖ ≤ M := by
  obtain ⟨C, hCc, hCx⟩ := hC
  have hK : IsCompact (C ×ˢ Set.Icc (-1 : ℝ) 1) := hCc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨M, fun x t ht => ?_⟩
  obtain ⟨γ, hγ, hxγ⟩ := hCx x
  have h1 : g x = g (x - γ) := by
    have := hgp γ hγ (x - γ)
    rw [add_sub_cancel] at this
    exact this
  rw [h1]
  exact hM (x - γ, t) ⟨hxγ, ht⟩

theorem UpperTheory.eisenstein_period_derivative :
    UpperTheory.V.Sd.Eis.PerDeriv := by
  intro A _ _ _ _ _ _ Γ hC μ D hDt f f' hf hf' hfp hf'p hd
  obtain ⟨M, hM⟩ := UpperTheory.exists_bound_of_continuous_periodic_cocompact A Γ hC f' hf' hf'p
  obtain ⟨N, hN⟩ := UpperTheory.exists_bound_of_continuous_periodic_cocompact A Γ hC f hf hfp
  have hslice : ∀ (g : A → ℝ → ℂ), Continuous (Function.uncurry g) → ∀ t : ℝ, Continuous (fun x => g x t) :=
    fun g hg t => hg.comp (continuous_id.prodMk continuous_const)
  haveI hfin : MeasureTheory.IsFiniteMeasure (μ.restrict D) := MeasureTheory.isFiniteMeasure_restrict.2 hDt
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict D)
    (F := fun t x => f x t) (F' := fun t x => f' x t) (x₀ := (0 : ℝ)) (bound := fun _ => M)
    (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun t => (hslice f hf t).aestronglyMeasurable)
    (MeasureTheory.Measure.integrableOn_of_bounded (M := N) hDt (hslice f hf 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hN x 0 ⟨by norm_num, by norm_num⟩))
    (hslice f' hf' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t ht => hM x t ht)
    (MeasureTheory.integrable_const M)
    (Filter.Eventually.of_forall fun x t _ => hd x t)
  exact key.2
