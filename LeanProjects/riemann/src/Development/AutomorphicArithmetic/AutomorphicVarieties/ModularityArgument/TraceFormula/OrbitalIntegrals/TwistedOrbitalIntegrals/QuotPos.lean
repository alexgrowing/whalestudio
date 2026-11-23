import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotPos :
    UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotInt → UpperTheory.V.Z.Tf.Orb.QuotMass → UpperTheory.V.Z.Tf.Orb.QuotPos := by
  intro _ hInt hMass G _ _ _ _ _ _ _ _ μG hμG H hH μ hμ hinv hex F hF hFH hC hnn hne
  have hρ := hex.choose_spec
  rw [quotIntegral, dif_pos hex]
  generalize hex.choose = ρ at hρ
  have hI := hInt G μG hμG H hH μ hμ hinv F hF hFH hC ρ hρ
  have hfin := (hMass G μG hμG H hH μ hμ hinv ρ hρ).1
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : SFinite μ := inferInstance
  have hre : (∫ g, F g * ((ρ g).toReal : ℂ) ∂μG).re = ∫ g, (F g).re * (ρ g).toReal ∂μG := by
    have := integral_re hI
    simpa using this.symm
  have hI' : Integrable (fun g => (F g).re * (ρ g).toReal) μG := by
    simpa using hI.re
  rw [hre]
  have h0 : 0 ≤ fun g => (F g).re * (ρ g).toReal := fun g => mul_nonneg (hnn g) ENNReal.toReal_nonneg
  refine lt_of_le_of_ne (integral_nonneg h0) fun hz => ?_
  have hae := (integral_eq_zero_iff_of_nonneg h0 hI').1 hz.symm
  set Φ : G → ℝ≥0∞ := fun g => ENNReal.ofReal (F g).re with hΦ
  have hΦc : Continuous Φ := ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp hF)
  have hΦm : Measurable Φ := hΦc.measurable
  have h1 : ∫⁻ g, Φ g * ρ g ∂μG = 0 := by
    refine (lintegral_eq_zero_iff (f := fun g => Φ g * ρ g) (hΦm.mul hρ.1)).2 ?_
    filter_upwards [hae, hfin] with g hg hg'
    simp only [Pi.zero_apply, mul_eq_zero, ENNReal.toReal_eq_zero_iff] at hg ⊢
    rcases hg with hg | hg | hg
    · left; simp [hΦ, hg]
    · right; exact hg
    · exact absurd hg hg'
  have hmul : Measurable fun p : G × H => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have h2 : ∫⁻ g, Φ g ∂μG = 0 := by
    calc ∫⁻ g, Φ g ∂μG = ∫⁻ g, ∫⁻ h : H, Φ g * ρ ((h : G) * g) ∂μ ∂μG := by
          refine lintegral_congr fun g => ?_
          rw [lintegral_const_mul, hρ.2 g, mul_one]
          exact hρ.1.comp (measurable_subtype_coe.mul_const g)
      _ = ∫⁻ h : H, ∫⁻ g, Φ g * ρ ((h : G) * g) ∂μG ∂μ :=
          lintegral_lintegral_swap ((hΦm.comp measurable_fst).mul (hρ.1.comp hmul)).aemeasurable
      _ = ∫⁻ _h : H, 0 ∂μ := by
          refine lintegral_congr fun h => ?_
          rw [← h1, ← lintegral_mul_left_eq_self (fun g => Φ g * ρ g) (h : G)]
          refine lintegral_congr fun g => ?_
          simp only [hΦ, hFH _ h.2]
      _ = 0 := lintegral_zero
  rw [lintegral_eq_zero_iff hΦm] at h2
  have h3 : Φ = 0 := (Continuous.ae_eq_iff_eq μG hΦc continuous_zero).1 h2
  obtain ⟨g, hg⟩ := hne
  have h4 := congrFun h3 g
  simp only [hΦ, Pi.zero_apply, ENNReal.ofReal_eq_zero] at h4
  exact hg (le_antisymm h4 (hnn g))
