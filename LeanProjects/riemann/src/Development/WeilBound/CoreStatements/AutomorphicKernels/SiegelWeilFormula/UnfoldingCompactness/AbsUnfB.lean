import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.AbsUnfA

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.SiegelWeilFormula.kunf

theorem abs_integrable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (lam : Measure V) [lam.IsAddHaarMeasure]
    (Λ : AddSubgroup V) [Countable Λ] (𝓖 : Set V) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam)
    {Q : Type} [Countable Q] (act : Q → Λ → Q) (hact0 : ∀ q, act q 0 = q)
    (hact : ∀ q ν ν', act (act q ν) ν' = act q (ν + ν'))
    (A : Q → V → ℂ) (hA : ∀ q, Continuous (A q)) (hAact : ∀ q ν β, A (act q ν) β = A q (β + (ν : V)))
    (C : Set V) (hC : IsCompact C) (hcov : ∀ β, ∃ ν : Λ, β + (ν : V) ∈ C)
    (u : Q → ℝ) (hu : Summable u) (hAu : ∀ q, ∀ β ∈ C, ‖A q β‖ ≤ u q)
    (q₀ : Q) (hinj : Function.Injective (act q₀)) : Integrable (A q₀) lam := by
  have hAm : ∀ q, Measurable fun β => ‖A q β‖ₑ := fun q => (hA q).measurable.enorm
  obtain ⟨S, hS_def⟩ : ∃ S : V → ℝ≥0∞, S = fun β => ∑' q, ‖A q β‖ₑ := ⟨_, rfl⟩
  have hSm : Measurable S := by
    rw [hS_def]
    exact Measurable.ennreal_tsum fun q => hAm q
  have hSper : ∀ (ν : Λ) β, S (β + ν) = S β := by
    intro ν β
    let e : Q ≃ Q := ⟨fun q => act q ν, fun q => act q (-ν),
      fun q => show act (act q ν) (-ν) = q by rw [hact, add_neg_cancel, hact0],
      fun q => show act (act q (-ν)) ν = q by rw [hact, neg_add_cancel, hact0]⟩
    rw [hS_def]
    simp only [← hAact]
    exact e.tsum_eq (fun q => ‖A q β‖ₑ)
  obtain ⟨ν₀, hν₀⟩ := hcov 0
  have hu0 : ∀ q, 0 ≤ u q := fun q => (norm_nonneg _).trans (hAu q _ hν₀)
  have hM : (∑' q, ENNReal.ofReal (u q)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hu0 hu]
    exact ENNReal.ofReal_ne_top
  have hmeas : ∀ ν : Λ, AEMeasurable (fun β => ‖A q₀ (ν +ᵥ β)‖ₑ) (lam.restrict 𝓖) := fun ν =>
    ((hA q₀).comp (continuous_const_add (ν : V))).measurable.enorm.aemeasurable
  have h1 : ∫⁻ β, ‖A q₀ β‖ₑ ∂lam ≤ ∫⁻ β in 𝓖, S β ∂lam := by
    rw [h𝓖.lintegral_eq_tsum'', ← lintegral_tsum hmeas]
    refine lintegral_mono fun β => ?_
    have h5 : ∀ ν : Λ, ‖A q₀ (ν +ᵥ β)‖ₑ = ‖A (act q₀ ν) β‖ₑ := fun ν => by
      show ‖A q₀ ((ν : V) + β)‖ₑ = _
      rw [hAact, add_comm]
    simp only [h5, hS_def]
    exact ENNReal.tsum_comp_le_tsum_of_injective hinj (fun q => ‖A q β‖ₑ)
  have h2 : ∫⁻ β in 𝓖, S β ∂lam ≤ ∫⁻ β in C, S β ∂lam := lintegral_fd_le h𝓖 S hSper hcov
  have h3 : ∫⁻ β in C, S β ∂lam ≤ ∫⁻ _ in C, (∑' q, ENNReal.ofReal (u q)) ∂lam := by
    apply lintegral_mono_ae
    rw [ae_restrict_iff (measurableSet_le hSm measurable_const)]
    refine Filter.Eventually.of_forall fun β hβ => ?_
    rw [hS_def]
    exact ENNReal.tsum_le_tsum fun q => by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hAu q β hβ)
  rw [setLIntegral_const] at h3
  refine ⟨(hA q₀).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (h1.trans (h2.trans h3)) (ENNReal.mul_lt_top hM.lt_top hC.measure_lt_top)

end PositivityTheory.SiegelWeilFormula.kunf

end
