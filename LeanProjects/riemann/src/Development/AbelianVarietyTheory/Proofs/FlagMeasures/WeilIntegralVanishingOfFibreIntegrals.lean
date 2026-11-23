import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCutoffFibreIntegralOneSubgroup

open MeasureTheory GlobalTheory.Dec

namespace GlobalTheory.Dec

theorem integral_mul_eq_zero_of_cutoff {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hβt : ∀ y, β y ≠ ⊤) (hβ1 : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (F φ : G → ℂ) (hF : Measurable F) (hφ : Measurable φ) (hinv : ∀ᵐ m ∂ν, ∀ y, F (m * y) = F y)
    (hint : Integrable (fun y => F y * φ y) μ) (h0 : ∀ y, ∫ m, φ (m * y) ∂ν = 0) :
    ∫ y, F y * φ y ∂μ = 0 := by
  set f : G × G → ℂ := fun p => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * (F p.2 * φ p.2) with hf_def
  have hβm : Measurable fun p : G × G => β (p.1⁻¹ * p.2) :=
    hβ.comp (measurable_fst.inv.mul measurable_snd)
  have hfm : Measurable f :=
    (Complex.measurable_ofReal.comp hβm.ennreal_toReal).mul
      ((hF.comp measurable_snd).mul (hφ.comp measurable_snd))

  have hβy : ∀ y, Measurable fun m : G => β (m⁻¹ * y) := fun y =>
    hβ.comp (measurable_inv.mul_const y)
  have hfib : ∀ y, ∫ m, (β (m⁻¹ * y)).toReal ∂ν = 1 := by
    intro y
    rw [integral_toReal (hβy y).aemeasurable (Filter.Eventually.of_forall fun m => (hβt _).lt_top),
      hβ1 y, ENNReal.toReal_one]
  have hfibI : ∀ y, Integrable (fun m => (β (m⁻¹ * y)).toReal) ν := fun y =>
    integrable_toReal_of_lintegral_ne_top (hβy y).aemeasurable (by rw [hβ1 y]; exact ENNReal.one_ne_top)

  have hA : ∫ y, F y * φ y ∂μ = ∫ y, ∫ m, f (m, y) ∂ν ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hf_def]
    rw [integral_mul_const, integral_complex_ofReal, hfib y]
    simp

  have hfI : Integrable f (ν.prod μ) := by
    rw [integrable_prod_iff' hfm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · simp only [hf_def]
      exact (hfibI y).ofReal.mul_const _
    · have hn : (fun y => ∫ m, ‖f (m, y)‖ ∂ν) = fun y => ‖F y * φ y‖ := by
        funext y
        simp only [hf_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, ENNReal.abs_toReal]
        rw [integral_mul_const, hfib y, one_mul]
      rw [hn]
      exact hint.norm

  have hmp : MeasurePreserving (fun p : G × G => (p.1, p.1 * p.2)) (ν.prod μ) (ν.prod μ) :=
    measurePreserving_prod_mul ν μ
  have hemb : MeasurableEmbedding (fun p : G × G => (p.1, p.1 * p.2)) :=
    (MeasurableEquiv.shearMulRight G).measurableEmbedding
  have hae : ∀ᵐ p ∂(ν.prod μ),
      f (p.1, p.1 * p.2) = ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)) := by
    have h1 : ∀ᵐ p ∂(ν.prod μ), ∀ y, F (p.1 * y) = F y :=
      Measure.quasiMeasurePreserving_fst.ae hinv
    filter_upwards [h1] with p hp
    simp only [hf_def, inv_mul_cancel_left, hp]
  have hgI : Integrable (fun p : G × G => ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)))
      (ν.prod μ) :=
    ((hmp.integrable_comp_emb hemb).2 hfI).congr hae
  calc ∫ y, F y * φ y ∂μ
      = ∫ p, ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)) ∂(ν.prod μ) := by
        rw [hA, ← integral_prod_symm f hfI, ← hmp.integral_comp hemb f]
        exact integral_congr_ae hae
    _ = ∫ z, ∫ m, ((β z).toReal : ℂ) * (F z * φ (m * z)) ∂ν ∂μ := integral_prod_symm _ hgI
    _ = 0 := by
        have hz : ∀ z, ∫ m, ((β z).toReal : ℂ) * (F z * φ (m * z)) ∂ν = 0 := by
          intro z
          simp_rw [← mul_assoc]
          rw [integral_const_mul, h0 z, mul_zero]
        simp only [hz, integral_zero]

theorem weilVanish : WeilVanish := by
  unfold WeilVanish
  intro G _ _ _ _ _ _ _ _ μ _ N ν hN hν F φ hF hφ hinv hint h0
  obtain ⟨β, hβ, hβt, hβ1⟩ := exists_measurable_cutoff_fibre_integral_one G N ν hN hν
  haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
  have hN' : ∀ᵐ m ∂ν, m ∈ (N : Set G) := mem_ae_iff.2 hν.2.2.1
  have hae : ∀ᵐ m ∂ν, ∀ y, F (m * y) = F y := hN'.mono fun m hm y => hinv m hm y
  exact integral_mul_eq_zero_of_cutoff μ ν β hβ hβt hβ1 F φ hF hφ hae hint h0

end GlobalTheory.Dec
