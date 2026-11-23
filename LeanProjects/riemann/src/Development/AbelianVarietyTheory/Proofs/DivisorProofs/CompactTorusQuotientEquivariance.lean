import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMeasure
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.ParabolicCoord

theorem integral_weight_mul_coordMeasure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (T : Type) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T]
    [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (Q : Subgroup G) (κ : K →* G) (m : T →* G) (δ : T →* ℝ≥0) (μK : Measure K) (μT : Measure T) (μQ : Measure Q),
    IsClosed (Q : Set G) → Continuous κ → Topology.IsClosedEmbedding m → Continuous δ → μK.IsHaarMeasure → μT.IsHaarMeasure → μQ.IsHaarMeasure →
    ∀ β : G → ℝ≥0, Measurable β → (∀ x, ∫⁻ q : Q, (β (q * x) : ℝ≥0∞) ∂μQ = 1) →
    ∀ f : G → ℂ, Continuous f → (∀ q ∈ Q, ∀ x, f (q * x) = f x) →
    ∀ g, Integrable (fun p : K × T => f ((m p.2)⁻¹ * κ p.1 * g) * ((δ p.2 : ℝ) : ℂ)) (μK.prod μT) →
    ∫ x, ((β (x * g) : ℝ) : ℂ) * f (x * g) ∂(GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK) = ∫ k, ∫ t, f ((m t)⁻¹ * κ k * g) * ((δ t : ℝ) : ℂ) ∂μT ∂μK := by
  intro G _ _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ Q κ m δ μK μT μQ hQ hκ hm hδ
    hμK hμT hμQ β hβ hβ1 f hf hfQ g hint
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology (Q : Set G)
  haveI : SigmaCompactSpace Q := inferInstance
  haveI : IsLocallyFiniteMeasure μQ := inferInstance
  haveI : SigmaFinite μQ := inferInstance
  haveI : SigmaFinite μT := inferInstance
  have hδm : Measurable (fun t => δ t) := hδ.measurable
  have hmc : Continuous m := hm.continuous
  set ν : Measure T := μT.withDensity fun t => ((δ t : ℝ≥0) : ℝ≥0∞) with hν
  haveI : SFinite ν := inferInstance
  set y : K → T → G := fun k t => (m t)⁻¹ * κ k * g with hy
  have hyc : Continuous (fun p : K × T => y p.1 p.2) := by
    simp only [hy]; fun_prop
  have hyc' : Continuous (fun p : K × (T × Q) => y p.1 p.2.1) :=
    hyc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hqy : Measurable (fun p : K × (T × Q) => (p.2.2 : G) * y p.1 p.2.1) :=
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).mul hyc' |>.measurable
  let H : K × (T × Q) → ℂ := fun p => ((β ((p.2.2 : G) * y p.1 p.2.1) : ℝ) : ℂ) * f (y p.1 p.2.1)
  have hHm : Measurable H :=
    (Complex.measurable_ofReal.comp (measurable_coe_nnreal_real.comp (hβ.comp hqy))).mul
      (hf.comp hyc').measurable
  have hφ : Continuous (fun p : K × (T × Q) => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1) := by fun_prop
  have hFm : Measurable (fun x : G => ((β (x * g) : ℝ) : ℂ) * f (x * g)) :=
    (Complex.measurable_ofReal.comp (measurable_coe_nnreal_real.comp
      (hβ.comp (measurable_mul_const g)))).mul (hf.measurable.comp (measurable_mul_const g))
  have hcomp : ∀ p : K × (T × Q),
      ((β ((p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1 * g) : ℝ) : ℂ) * f ((p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1 * g) = H p := by
    intro p
    have e : (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1 * g = (p.2.2 : G) * y p.1 p.2.1 := by
      simp only [hy]; group
    simp only [H, e, hfQ _ p.2.2.2]

  have hβlin : ∀ x : G, Measurable (fun q : Q => (β ((q : G) * x) : ℝ≥0∞)) := fun x =>
    measurable_coe_nnreal_ennreal.comp (hβ.comp (measurable_subtype_coe.mul_const x))
  have hβint : ∀ x : G, ∫ q : Q, ((β ((q : G) * x) : ℝ) : ℂ) ∂μQ = 1 := by
    intro x
    rw [integral_complex_ofReal]
    have : ∫ q : Q, (β ((q : G) * x) : ℝ) ∂μQ = (∫⁻ q : Q, (β ((q : G) * x) : ℝ≥0∞) ∂μQ).toReal := by
      rw [← integral_toReal (hβlin x).aemeasurable (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
      rfl
    rw [this, hβ1 x]; simp

  have hHint : Integrable H (μK.prod (ν.prod μQ)) := by
    refine ⟨hHm.aestronglyMeasurable, ?_⟩
    have hn : ∀ p, ‖H p‖ₑ = (β ((p.2.2 : G) * y p.1 p.2.1) : ℝ≥0∞) * ‖f (y p.1 p.2.1)‖ₑ := by
      intro p
      simp only [H, enorm_eq_nnnorm, nnnorm_mul, ENNReal.coe_mul]
      congr 2
      simp
    have hAm : Measurable fun p : K × (T × Q) =>
        (β ((p.2.2 : G) * y p.1 p.2.1) : ℝ≥0∞) * ‖f (y p.1 p.2.1)‖ₑ :=
      (measurable_coe_nnreal_ennreal.comp (hβ.comp hqy)).mul (hf.comp hyc').measurable.enorm
    unfold HasFiniteIntegral
    simp_rw [hn]
    rw [lintegral_prod _ hAm.aemeasurable]
    have hin : ∀ k, ∫⁻ tq : T × Q, (β ((tq.2 : G) * y k tq.1) : ℝ≥0∞) * ‖f (y k tq.1)‖ₑ ∂(ν.prod μQ)
        = ∫⁻ t, ‖f (y k t) * ((δ t : ℝ) : ℂ)‖ₑ ∂μT := by
      intro k
      rw [lintegral_prod (fun tq : T × Q => (β ((tq.2 : G) * y k tq.1) : ℝ≥0∞) * ‖f (y k tq.1)‖ₑ)
        (hAm.comp measurable_prodMk_left).aemeasurable]
      have h2 : ∀ t, ∫⁻ q : Q, (β ((q : G) * y k t) : ℝ≥0∞) * ‖f (y k t)‖ₑ ∂μQ = ‖f (y k t)‖ₑ := by
        intro t
        rw [lintegral_mul_const _ (hβlin _), hβ1, one_mul]
      simp_rw [h2]
      have hgm : Measurable (fun t => ‖f (y k t)‖ₑ) :=
        (hf.comp (hyc.comp (continuous_const.prodMk continuous_id))).measurable.enorm
      rw [hν, lintegral_withDensity_eq_lintegral_mul _ hδm.coe_nnreal_ennreal hgm]
      refine lintegral_congr fun t => ?_
      simp only [Pi.mul_apply, enorm_eq_nnnorm, nnnorm_mul, ENNReal.coe_mul]
      rw [mul_comm]; congr 2
      simp
    simp_rw [hin]
    have hB := hint.hasFiniteIntegral
    unfold HasFiniteIntegral at hB
    rwa [lintegral_prod _ (hint.aestronglyMeasurable.enorm)] at hB
  unfold coordMeasure
  rw [integral_map hφ.measurable.aemeasurable hFm.aestronglyMeasurable]
  simp_rw [hcomp]
  rw [integral_prod H hHint]
  refine integral_congr_ae ?_
  filter_upwards [hHint.prod_right_ae] with k hk
  rw [integral_prod _ hk]
  have h3 : ∀ t, ∫ q : Q, H (k, (t, q)) ∂μQ = f (y k t) := by
    intro t
    simp only [H]
    rw [integral_mul_const, hβint, one_mul]
  simp_rw [h3]
  rw [hν, integral_withDensity_eq_integral_smul hδm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [NNReal.smul_def, Complex.real_smul, hy]
  ring

end GlobalTheory.ParabolicCoord
