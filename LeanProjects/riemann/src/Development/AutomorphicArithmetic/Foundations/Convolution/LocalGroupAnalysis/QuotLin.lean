import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.G

section

variable {G T : Type} [Group G] [MeasurableSpace G] [Group T] [MeasurableSpace T]

private theorem smul_coe (a : NNReal) (μ : Measure G) : a • μ = (a : ℝ≥0∞) • μ := rfl

private theorem uni_smul [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] {μ : Measure G}
    (h : Uni μ) {a : NNReal} (ha : a ≠ 0) : Uni (a • μ) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨Measure.IsHaarMeasure.nnreal_smul μ ha,
    ⟨by rw [Measure.inv, Measure.map_smul, Measure.map_inv_eq_self]⟩⟩

private theorem isNrm_div {j : T →* G} {ν : Measure T} {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ)
    {b : NNReal} (hb : b ≠ 0) : IsNrm j (b • ν) (fun x => (b : ℝ≥0∞)⁻¹ * ρ x) := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by simpa using hb
  refine ⟨h.1.const_mul _, fun x => ?_⟩
  rw [smul_coe, lintegral_smul_measure, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hb0), h.2 x,
    mul_one, smul_eq_mul, ENNReal.mul_inv_cancel hb0 ENNReal.coe_ne_top]

private theorem isNrm_mul {j : T →* G} {ν : Measure T} {ρ : G → ℝ≥0∞} {b : NNReal}
    (h : IsNrm j (b • ν) ρ) : IsNrm j ν (fun x => (b : ℝ≥0∞) * ρ x) := by
  refine ⟨h.1.const_mul _, fun x => ?_⟩
  have := h.2 x
  rw [smul_coe, lintegral_smul_measure, smul_eq_mul] at this
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, this]

private theorem mul_toReal (z : ℂ) (b : NNReal) (r : ℝ≥0∞) :
    z * ((((b : ℝ≥0∞)⁻¹ * r).toReal : ℝ) : ℂ) = (((b : ℝ) : ℂ))⁻¹ * (z * ((r.toReal : ℝ) : ℂ)) := by
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.coe_toReal]
  push_cast
  ring

private theorem int_iff {μ : Measure G} {F : G → ℂ} {ρ : G → ℝ≥0∞} {a b : NNReal} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    Integrable (fun x => F x * ((((b : ℝ≥0∞)⁻¹ * ρ x).toReal : ℝ) : ℂ)) (a • μ) ↔
      Integrable (fun x => F x * (((ρ x).toReal : ℝ) : ℂ)) μ := by
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by simpa using ha
  have hc : ((b : ℝ) : ℂ) ≠ 0 := by simpa using hb
  rw [smul_coe, integrable_smul_measure ha0 ENNReal.coe_ne_top]
  simp only [mul_toReal]
  constructor
  · intro h
    have := h.const_mul (((b : ℝ) : ℂ))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    exact mul_inv_cancel_left₀ hc _
  · exact fun h => h.const_mul _

private theorem qInt_iff {μ : Measure G} {j : T →* G} {ν : Measure T} {F : G → ℂ} {a b : NNReal}
    (ha : a ≠ 0) (hb : b ≠ 0) : QInt (a • μ) j (b • ν) F ↔ QInt μ j ν F := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by simpa using hb
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun ρ hρ => (int_iff ha hb).1 (h3 _ (isNrm_div hρ hb))⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun ρ hρ => ?_⟩
    have := (int_iff (μ := μ) (ρ := fun x => (b : ℝ≥0∞) * ρ x) (F := F) ha hb).2 (h3 _ (isNrm_mul hρ))
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel hb0 ENNReal.coe_ne_top, one_mul] using this

end

end UpperTheory.ConvolutionTheory.G

open UpperTheory.ConvolutionTheory.G in
theorem UpperTheory.ConvolutionTheory.G.quotLin_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotLin := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP
  obtain ⟨ρ₀, -, hρ₀, -⟩ := hN G T μ j ν hP
  refine ⟨fun ι s c F hF => ?_, fun a b ha hb => ?_⟩
  · have hsum : QInt μ j ν (fun g => ∑ i ∈ s, c i * F i g) := by
      refine ⟨Finset.measurable_sum s fun i hi => measurable_const.mul (hF i hi).1,
        fun t g => Finset.sum_congr rfl fun i hi => by rw [(hF i hi).2.1], fun ρ hρ => ?_⟩
      have := integrable_finset_sum s (fun i hi => ((hF i hi).2.2 ρ hρ).const_mul (c i))
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Finset.sum_mul, mul_assoc]
    refine ⟨hsum, ?_⟩
    rw [(hE G T μ j ν hP _ hsum.1 hsum.2.1 _ hρ₀).2.2,
      Finset.sum_congr rfl fun i hi => by
        rw [(hE G T μ j ν hP _ (hF i hi).1 (hF i hi).2.1 _ hρ₀).2.2]]
    simp only [Finset.sum_mul, mul_assoc]
    rw [integral_finset_sum s fun i hi => ((hF i hi).2.2 _ hρ₀).const_mul (c i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · have hP' : Pair (a • μ) j (b • ν) := ⟨uni_smul hP.1 ha, hP.2.1, uni_smul hP.2.2 hb⟩
    refine ⟨hP', fun F hF hinv => ⟨qInt_iff ha hb, ?_⟩⟩
    have hbC : ((b : ℝ) : ℂ) ≠ 0 := by simpa using hb
    rw [(hE G T _ _ _ hP' F hF hinv _ (isNrm_div hρ₀ hb)).2.2, (hE G T μ j ν hP F hF hinv _ hρ₀).2.2,
      integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    simp only [mul_toReal]
    rw [integral_const_mul]
    push_cast
    field_simp
