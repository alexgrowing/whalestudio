import Mathlib

open MeasureTheory

theorem UpperTheory.innerProduct_integral_fundamentalDomain_of_compact :
    ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure] (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ Ω : Set H, IsCompact Ω → (∀ g, ∃ γ ∈ Γ, γ * g ∈ Ω) → ∀ f g : H → ℂ, Continuous f → Continuous g → (∀ γ ∈ Γ, ∀ h, f (γ * h) = f h) → (∀ γ ∈ Γ, ∀ h, g (γ * h) = g h) → IntegrableOn (fun h => f h * starRingEnd ℂ (g h)) 𝓕 μ ∧ (∀ y, ∫ h in 𝓕, f (h * y) * starRingEnd ℂ (g (h * y)) ∂μ = ∫ h in 𝓕, f h * starRingEnd ℂ (g h) ∂μ) ∧ (f ≠ 0 → 0 < (∫ h in 𝓕, f h * starRingEnd ℂ (f h) ∂μ).re) := by
  intro H _ _ _ _ _ μ _ _ _ Γ _ 𝓕 h𝓕 hfin Ω hΩ hcov f g hf hg hfi hgi
  have bdd : ∀ u : H → ℂ, Continuous u → (∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) → ∃ C, ∀ h, ‖u h‖ ≤ C := by
    intro u hu hinv
    obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hu.continuousOn
    refine ⟨C, fun h => ?_⟩
    obtain ⟨γ, hγ, hmem⟩ := hcov h
    rw [← hinv γ hγ h]
    exact hC _ hmem
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.mpr hfin.ne
  have intg : ∀ u : H → ℂ, Continuous u → (∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) → IntegrableOn u 𝓕 μ := by
    intro u hu hinv
    obtain ⟨C, hC⟩ := bdd u hu hinv
    exact Integrable.of_bound hu.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  set u : H → ℂ := fun h => f h * starRingEnd ℂ (g h) with hu_def
  have hu : Continuous u := hf.mul (Complex.continuous_conj.comp hg)
  have hui : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h := by
    intro γ hγ h
    simp [u, hfi γ hγ, hgi γ hγ]
  refine ⟨intg u hu hui, ?_, ?_⟩
  · intro y
    let t := (fun h => h * y⁻¹) ⁻¹' 𝓕
    have ht : IsFundamentalDomain Γ t μ :=
      h𝓕.preimage_of_equiv (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
        (e := id) Function.bijective_id (fun γ x => by
          simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have hset : 𝓕 = (fun h => h * y) ⁻¹' t := by
      ext h
      simp [t]
    have h1 : ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in t, u h ∂μ := by
      rw [hset]
      exact (measurePreserving_mul_right μ y).setIntegral_preimage_emb
        (MeasurableEquiv.mulRight y).measurableEmbedding u t
    have h2 : ∫ h in t, u h ∂μ = ∫ h in 𝓕, u h ∂μ :=
      ht.setIntegral_eq h𝓕 (fun γ x => by
        simp only [Subgroup.smul_def, smul_eq_mul]
        exact hui γ γ.2 x)
    exact h1.trans h2
  · intro hne
    have hff : ∀ h, f h * starRingEnd ℂ (f h) = ((Complex.normSq (f h) : ℝ) : ℂ) :=
      fun h => Complex.mul_conj _
    simp_rw [hff]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    have hnn : 0 ≤ fun h => Complex.normSq (f h) := fun h => Complex.normSq_nonneg _
    have hint : IntegrableOn (fun h => Complex.normSq (f h)) 𝓕 μ := by
      have := (intg (fun h => f h * starRingEnd ℂ (f h)) (hf.mul (Complex.continuous_conj.comp hf))
        (fun γ hγ h => by simp [hfi γ hγ])).re
      simp only [hff, Complex.ofReal_re] at this
      exact this
    refine lt_of_le_of_ne (integral_nonneg hnn) (fun h0 => hne ?_)
    have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp h0.symm
    have hae' : (fun h => ‖f h‖ₑ) =ᵐ[μ.restrict 𝓕] 0 := by
      filter_upwards [hae] with h hh
      simp only [Pi.zero_apply, Complex.normSq_eq_zero] at hh
      simp [hh]
    have hl𝓕 : ∫⁻ h in 𝓕, ‖f h‖ₑ ∂μ = 0 := by
      rw [lintegral_congr_ae hae']
      simp
    have hlall : ∫⁻ h, ‖f h‖ₑ ∂μ = 0 := by
      rw [h𝓕.lintegral_eq_tsum'']
      have : ∀ γ : Γ, ∫⁻ x in 𝓕, ‖f (γ • x)‖ₑ ∂μ = 0 := by
        intro γ
        simp only [Subgroup.smul_def, smul_eq_mul, hfi γ γ.2]
        exact hl𝓕
      simp [this]
    have hz := (lintegral_eq_zero_iff' hf.enorm.aemeasurable).mp hlall
    have hz' : f =ᵐ[μ] fun _ => (0 : ℂ) := by
      filter_upwards [hz] with h hh
      simpa using hh
    exact (Continuous.ae_eq_iff_eq μ hf continuous_const).mp hz'
