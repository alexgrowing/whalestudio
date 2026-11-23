import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

open MeasureTheory Topology
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.G

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {T : Type} [Group T] [TopologicalSpace T]
    [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] {μ : Measure G} {j : T →* G} {ν : Measure T}

private theorem lint_eq (hp : Pair μ j ν) {Φ : G → ℝ≥0∞} (hΦ : Measurable Φ) (hi : ∀ t g, Φ (j t * g) = Φ g)
    {ρ ρ' : G → ℝ≥0∞} (h : IsNrm j ν ρ) (h' : IsNrm j ν ρ') :
    ∫⁻ x, Φ x * ρ x ∂μ = ∫⁻ x, Φ x * ρ' x ∂μ := by
  obtain ⟨⟨hμ, -⟩, hj, hν, hν'⟩ := hp
  have hjm : Measurable j := hj.continuous.measurable
  have hm := h.1
  have hm' := h'.1
  calc ∫⁻ x, Φ x * ρ x ∂μ = ∫⁻ x, ∫⁻ t, Φ x * ρ x * ρ' (j t * x) ∂ν ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul _ (by fun_prop), h'.2, mul_one]
    _ = ∫⁻ t, ∫⁻ x, Φ x * ρ x * ρ' (j t * x) ∂μ ∂ν :=
        lintegral_lintegral_swap (Measurable.aemeasurable (by unfold Function.uncurry; fun_prop))
    _ = ∫⁻ t, ∫⁻ x, Φ x * ρ' x * ρ (j t⁻¹ * x) ∂μ ∂ν := by
        refine lintegral_congr fun t => ?_
        rw [← lintegral_mul_left_eq_self (μ := μ) (fun x => Φ x * ρ x * ρ' (j t * x)) (j t⁻¹)]
        refine lintegral_congr fun x => ?_
        rw [hi, ← mul_assoc (j t), ← map_mul, mul_inv_cancel, map_one, one_mul, mul_right_comm]
    _ = ∫⁻ x, ∫⁻ t, Φ x * ρ' x * ρ (j t⁻¹ * x) ∂ν ∂μ :=
        (lintegral_lintegral_swap (Measurable.aemeasurable (by unfold Function.uncurry; fun_prop))).symm
    _ = ∫⁻ x, Φ x * ρ' x ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul _ (by fun_prop), lintegral_inv_eq_self (μ := ν) (fun t => ρ (j t * x)), h.2,
          mul_one]

private theorem ae_lt_top_nrm (hp : Pair μ j ν) {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ) : ∀ᵐ x ∂μ, ρ x < ⊤ := by
  obtain ⟨⟨hμ, -⟩, hj, hν, hν'⟩ := hp
  have hjm : Measurable j := hj.continuous.measurable
  have hm := h.1
  have h1 : ∀ᵐ x ∂μ, ∀ᵐ t ∂ν, ρ (j t * x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ae_lt_top (by fun_prop) (by rw [h.2]; exact ENNReal.one_ne_top)
  have hs : MeasurableSet {p : G × T | ρ (j p.2 * p.1) < ⊤} :=
    measurableSet_lt (by fun_prop) measurable_const
  have h2 : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ρ (j t * x) < ⊤ := (Measure.ae_ae_comm hs).1 h1
  obtain ⟨t, ht⟩ := h2.exists
  have := (measurePreserving_mul_left μ (j t)⁻¹).quasiMeasurePreserving.ae ht
  simpa using this

private theorem map_eq (hp : Pair μ j ν) {F : G → ℂ} (hF : Measurable F) (hi : ∀ t g, F (j t * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (h : IsNrm j ν ρ) (h' : IsNrm j ν ρ') :
    (μ.withDensity ρ).map F = (μ.withDensity ρ').map F := by
  ext s hs
  have key := lint_eq hp (Φ := fun x => s.indicator 1 (F x)) ((measurable_one.indicator hs).comp hF)
    (fun t g => by rw [hi]) h h'
  have e : ∀ r : G → ℝ≥0∞, (μ.withDensity r).map F s = ∫⁻ x, s.indicator 1 (F x) * r x ∂μ := fun r => by
    rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs), ← lintegral_indicator (hF hs)]
    refine lintegral_congr fun x => ?_
    by_cases hx : F x ∈ s <;> simp [Set.indicator, hx]
  rw [e, e, key]

private theorem int_eq (hp : Pair μ j ν) {F : G → ℂ} (hF : Measurable F)
    {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ) :
    ∫ x, F x * ((ρ x).toReal : ℂ) ∂μ = ∫ z, z ∂((μ.withDensity ρ).map F) := by
  rw [integral_map hF.aemeasurable (by fun_prop),
    integral_withDensity_eq_integral_toReal_smul h.1 (ae_lt_top_nrm hp h)]
  simp only [Complex.real_smul, mul_comm]

private theorem integrable_iff (hp : Pair μ j ν) {F : G → ℂ} (hF : Measurable F)
    {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ) :
    Integrable (fun x => F x * ((ρ x).toReal : ℂ)) μ ↔ ∫⁻ x, ‖F x‖ₑ * ρ x ∂μ ≠ ⊤ := by
  have hm := h.1
  have e : ∫⁻ x, ‖F x * ((ρ x).toReal : ℂ)‖ₑ ∂μ = ∫⁻ x, ‖F x‖ₑ * ρ x ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_nrm hp h] with x hx
    rw [enorm_mul, ← ofReal_norm_eq_enorm ((ρ x).toReal : ℂ), Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  rw [← e, ← lt_top_iff_ne_top]
  exact ⟨fun h => h.2, fun h => ⟨Measurable.aestronglyMeasurable (by fun_prop), h⟩⟩

end

end UpperTheory.ConvolutionTheory.G

theorem UpperTheory.ConvolutionTheory.G.quotEq :
    UpperTheory.ConvolutionTheory.G.QuotEq := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hp F hF hi ρ h
  have h2 : QInt μ j ν F ↔ ∫⁻ x, ‖F x‖ₑ * ρ x ∂μ ≠ ⊤ := by
    refine ⟨fun hq => (integrable_iff hp hF h).1 (hq.2.2 ρ h), fun hq => ⟨hF, hi, fun ρ' h' => ?_⟩⟩
    rw [integrable_iff hp hF h', lint_eq hp (Φ := fun x => ‖F x‖ₑ) hF.enorm (fun t g => by rw [hi]) h' h]
    exact hq
  refine ⟨h2.trans (integrable_iff hp hF h).symm, h2, ?_⟩
  have hex : ∃ ρ, IsNrm j ν ρ := ⟨ρ, h⟩
  rw [qI, dif_pos hex, int_eq hp hF hex.choose_spec, int_eq hp hF h, map_eq hp hF hi hex.choose_spec h]
