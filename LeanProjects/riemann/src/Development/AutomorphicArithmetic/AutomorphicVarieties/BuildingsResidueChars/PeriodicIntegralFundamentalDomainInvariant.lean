import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
open UpperTheory.V.Sd.Eis
open MeasureTheory Measure Pointwise

private theorem perMean_fin {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [Countable Γ] (hc : Cocpt Γ) (μ : Measure A) [μ.IsAddHaarMeasure]
    (D : Set A) (hD : IsAddFundamentalDomain Γ D μ) : μ D ≠ ⊤ := by
  obtain ⟨C, hC, hcov⟩ := hc
  have h1 : D ⊆ ⋃ g : Γ, ((g +ᵥ C) ∩ D) := by
    intro x hx
    obtain ⟨γ, hγ, h⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨x - γ, h, ?_⟩, hx⟩
    change γ + (x - γ) = x
    abel
  have h2 : μ D ≤ μ C := by
    rw [hD.measure_eq_tsum C]
    exact (measure_mono h1).trans (measure_iUnion_le _)
  exact ne_top_of_le_ne_top hC.measure_lt_top.ne h2

private theorem perMean_key {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [Countable Γ] (μ : Measure A) [μ.IsAddHaarMeasure]
    (D : Set A) (hD : IsAddFundamentalDomain Γ D μ) (hfin : μ D ≠ ⊤) (e : A ≃ᵐ A) (c : NNReal)
    (he : μ.map e = c • μ) (σ : Γ → Γ) (hσ : Function.Bijective σ) (hs : ∀ (g : Γ) x, e ((σ g : A) + x) = (g : A) + e x)
    (f : A → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) :
    ∫ x in D, f (e x) ∂μ = ∫ x in D, f x ∂μ := by
  have hq : QuasiMeasurePreserving e μ μ := ⟨e.measurable, by rw [he]; exact Measure.smul_absolutelyContinuous⟩
  have hD' : IsAddFundamentalDomain Γ (e ⁻¹' D) μ := hD.preimage_of_equiv hq hσ (fun g x => hs g x)
  have hm : μ (e ⁻¹' D) = μ D := by
    have := hD'.measure_set_eq hD MeasurableSet.univ (fun g => by simp)
    simpa using this
  have h0 : μ D ≠ 0 := hD.measure_ne_zero (NeZero.ne μ)
  have hc : (c : ENNReal) = 1 := by
    rw [← e.map_apply, he, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hm
    exact (ENNReal.mul_left_inj h0 hfin).1 (by rw [hm, one_mul])
  have hc' : c = 1 := by exact_mod_cast hc
  rw [hc', one_smul] at he
  have h1 : ∫ x in D, f (e x) ∂μ = ∫ x in e ⁻¹' D, f (e x) ∂μ := by
    refine hD.setIntegral_eq hD' (fun g x => ?_)
    obtain ⟨g', rfl⟩ := hσ.2 g
    change f (e ((σ g' : A) + x)) = _
    rw [hs, hf _ g'.2]
  rw [h1, ← setIntegral_map_equiv, he]

theorem UpperTheory.periodic_integral_fundamentalDomain_invariant :
    UpperTheory.V.Sd.Eis.PerMean := by
  intro A _ _ _ _ _ _ _ _ Γ _ hc μ _ D hD
  have hfin := perMean_fin Γ hc μ D hD
  refine ⟨hfin, fun f hf => ⟨fun hcont => ?_, fun y => ?_, fun e he => ?_⟩⟩
  · obtain ⟨C, hC, hcov⟩ := hc
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
    refine Measure.integrableOn_of_bounded hfin hcont.aestronglyMeasurable (M := M) (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨γ, hγ, h⟩ := hcov x
    have := hf γ hγ (x - γ)
    rw [add_sub_cancel] at this
    rw [this]
    exact hM _ h
  · refine perMean_key Γ μ D hD hfin (MeasurableEquiv.addRight y) 1 ?_ id Function.bijective_id ?_ f hf
    · rw [one_smul]
      exact map_add_right_eq_self μ y
    · intro g x
      exact add_assoc _ _ _
  · haveI : (μ.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ e
    refine perMean_key Γ μ D hD hfin e.toHomeomorph.toMeasurableEquiv _
      (Measure.isAddLeftInvariant_eq_smul (μ.map e) μ)
      (fun g => ⟨e.symm g, (he _).1 (by simpa using g.2)⟩) ⟨fun a b h => ?_, fun b => ⟨⟨e b, (he _).2 b.2⟩, ?_⟩⟩ ?_ f hf
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
    · exact Subtype.ext (e.symm_apply_apply _)
    · intro g x
      change e (e.symm g + x) = g + e x
      rw [map_add, e.apply_symm_apply]
