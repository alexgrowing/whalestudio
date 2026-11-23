import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem setIntegral_eq_mass_mul_avg : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Per Γ Φ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ((μ 𝓕).toReal : ℂ) * avg Γ Φ := by
  intro G _ _ _ _ _ _ Γ hΓ mG hB μ 𝓕 hμ h𝓕 Φ hΦ
  obtain ⟨hd, K, hK, hcov⟩ := hΓ
  have e := hB.measurable_eq
  subst e
  letI : MeasurableSpace G := borel G
  haveI : Countable Γ := countable_of_discrete_addSubgroup Γ
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ h𝓕).ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.1.continuousOn
  have hb : ∀ x, ‖Φ x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    have := hC _ hk
    rwa [hΦ.2 γ hγ] at this
  have hint : IntegrableOn Φ 𝓕 μ :=
    Measure.integrableOn_of_bounded hfin hΦ.1.aestronglyMeasurable (M := C) (Filter.Eventually.of_forall hb)
  refine ⟨hne, hfin, hint, ?_⟩
  have hex := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov).1
  have hex' : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ₀, F₀, h⟩ := hex
    exact ⟨(μ₀, F₀), h⟩
  have hav : avg Γ Φ = ∫ x in hex'.choose.2, Φ x ∂hex'.choose.1 := by
    simp only [avg]
    rw [dif_pos hex']
  rw [hav]
  obtain ⟨hμ₀, hF₀, h1⟩ := hex'.choose_spec
  generalize hex'.choose = p at hμ₀ hF₀ h1 ⊢
  obtain ⟨μ₀, F₀⟩ := p
  simp only at hμ₀ hF₀ h1 ⊢
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul μ μ₀⟩
  have hac : μ ≪ μ₀ := hc ▸ Measure.smul_absolutelyContinuous
  have hF₀' : IsAddFundamentalDomain Γ F₀ μ := hF₀.mono hac
  have e1 : μ 𝓕 = μ F₀ := h𝓕.measure_eq hF₀'
  have e2 : ∫ x in 𝓕, Φ x ∂μ = ∫ x in F₀, Φ x ∂μ :=
    h𝓕.setIntegral_eq hF₀' fun g x => hΦ.2 g g.2 x
  rw [e1, e2, hc, Measure.restrict_smul, integral_smul_nnreal_measure, Measure.smul_apply, h1]
  simp [ENNReal.smul_def, NNReal.smul_def]

end GlobalTheory.CuspGeneric
