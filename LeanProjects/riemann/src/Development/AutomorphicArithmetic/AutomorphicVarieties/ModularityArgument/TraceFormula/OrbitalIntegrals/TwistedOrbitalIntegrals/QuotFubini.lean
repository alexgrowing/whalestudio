import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.quotFubini :
    UpperTheory.V.Z.Tf.Orb.QuotMass → UpperTheory.V.Z.Tf.Orb.QuotFubini := by
  intro hM G _ _ _ _ _ _ _ _ μG hμG H hH μ hμ hinv F hF hFH hsupp
  obtain ⟨Y, C, hY, hC, hsupp⟩ := hsupp
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  swap
  · simp only [quotIntegral, dif_neg hex, integral_zero]
  simp only [quotIntegral, dif_pos hex]
  have hρ := hex.choose_spec
  generalize hex.choose = ρ at hρ ⊢
  obtain ⟨hS, hfin⟩ := (hM G μG hμG H hH μ hμ hinv ρ hρ).2 C hC
  set S : Set G := {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} with hSdef
  obtain ⟨M, hMb⟩ := (hY.prod hC).exists_bound_of_continuousOn hF.continuousOn
  have h1 : Integrable (S.indicator fun g => (ρ g).toReal) μG := by
    rw [integrable_indicator_iff hS.measurableSet]
    exact integrable_toReal_of_lintegral_ne_top hρ.1.aemeasurable hfin
  have h2 : Integrable (Y.indicator fun _ => M) μG := by
    rw [integrable_indicator_iff hY.isClosed.measurableSet]
    exact integrableOn_const hY.measure_lt_top.ne
  have hint : Integrable (Function.uncurry fun g y => F y g * ((ρ g).toReal : ℂ)) (μG.prod μG) := by
    refine (h1.mul_prod h2).mono' ?_ (Filter.Eventually.of_forall ?_)
    · have a1 : Measurable fun p : G × G => F p.2 p.1 :=
        (hF.comp continuous_swap).measurable
      have a2 : Measurable fun p : G × G => ((ρ p.1).toReal : ℂ) :=
        Complex.measurable_ofReal.comp ((hρ.1.comp measurable_fst).ennreal_toReal)
      exact (a1.mul a2).aestronglyMeasurable
    · rintro ⟨g, y⟩
      show ‖F y g * ((ρ g).toReal : ℂ)‖ ≤ S.indicator (fun g => (ρ g).toReal) g * Y.indicator (fun _ => M) y
      by_cases h0 : F y g = 0
      · rw [h0, zero_mul, norm_zero]
        by_cases hg : g ∈ S
        · by_cases hy : y ∈ Y
          · obtain ⟨h, -, c, hc, -⟩ := hg
            have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMb (y, c) ⟨hy, hc⟩)
            exact mul_nonneg (Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) _)
              (Set.indicator_nonneg (fun _ _ => hM0) _)
          · rw [Set.indicator_of_notMem hy, mul_zero]
        · rw [Set.indicator_of_notMem hg, zero_mul]
      · obtain ⟨hy, hg⟩ := hsupp y g h0
        have hg' : g ∈ S := hg
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hg', norm_mul, Complex.norm_real,
          Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_comm]
        obtain ⟨h, hh, c, hc, rfl⟩ := hg
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        rw [hFH y h hh c]
        exact hMb (y, c) ⟨hy, hc⟩
  rw [← integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  exact (integral_mul_const _ _).symm
