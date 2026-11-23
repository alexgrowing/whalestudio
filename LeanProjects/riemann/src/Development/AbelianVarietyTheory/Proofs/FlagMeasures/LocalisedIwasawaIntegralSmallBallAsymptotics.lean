import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptoticStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdGaugeMeasuresGaugeBodyStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaFactorsNearOneGivenCompactFactorStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaProductGaugeSandwichNearOneStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoSmallBallDensityOfSqueezeStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem lintegral_triple_eq {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ₁ : Measure α) (μ₂ : Measure β) (μ₃ : Measure γ) [SFinite μ₂] [SFinite μ₃]
    (δ : β → ENNReal) (hδ : Measurable δ) (P : α × β × γ → ENNReal) (hP : Measurable P) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, P (u, m, k) ∂μ₃ ∂μ₂ ∂μ₁ = ∫⁻ x, δ x.2.1 * P x ∂(μ₁.prod (μ₂.prod μ₃)) := by
  symm
  rw [lintegral_prod (fun x => δ x.2.1 * P x)
    (show Measurable fun x : α × β × γ => δ x.2.1 * P x from (hδ.comp measurable_snd.fst).mul hP).aemeasurable]
  refine lintegral_congr fun u => ?_
  rw [lintegral_prod (fun y => δ y.1 * P (u, y))
    (show Measurable fun y : β × γ => δ y.1 * P (u, y) from
      (hδ.comp measurable_fst).mul (hP.comp measurable_prodMk_left)).aemeasurable]
  refine lintegral_congr fun m => ?_
  exact lintegral_const_mul (δ m)
    (show Measurable fun k : γ => P (u, m, k) from hP.comp (measurable_prodMk_left.comp measurable_prodMk_left))

theorem IsCut.sigmaFinite {n d : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)}
    {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsCut ε S E) {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : IsGaugeSub S d μ) : SigmaFinite μ := by
  obtain ⟨A, hA, hON, hspan, rfl⟩ := h
  exact (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hON hspan μ hμ).1

theorem localised_iwasawa_asymptotics : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsON EL → (∀ v, gau EN EM EK EL v = 0 → v = 0) → volume {v | gau EN EM EK EL v ≤ 1} ≠ ⊤ → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub (flagN ε W) dN μN → IsGaugeSub (flagM ε W) dM μM → IsGaugeSub (maxK ε) dK μK → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → Filter.Tendsto (fun r : ℝ => (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) * (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  intro n ε a j W hW dN dM dK dL EN EM EK EL hN hM hK hL hgau hvol μN μM μK hμN hμM hμK
  have := hN.sigmaFinite hμN
  have := hM.sigmaFinite hμM
  have := hK.sigmaFinite hμK
  obtain ⟨C, hC, hCη⟩ := GlobalTheory.T.iwasawa_product_gauge_sandwich_near_one n ε _ _ _ dN dM dK dL EN EM EK EL hN hM hK hL hgau
  obtain ⟨t₀, ht₀, hasym⟩ :=
    GlobalTheory.T.tendsto_prod_gaugeMeasures_gaugeBody n ε _ _ _ dN dM dK dL EN EM EK EL hN hM hK hgau μN μM μK hμN hμM hμK
  obtain ⟨t₁, ht₁, h₁⟩ := hCη 1 one_pos
  obtain ⟨ts, hts, hts0, hts1⟩ : ∃ ts : ℝ, 0 < ts ∧ ts ≤ t₀ ∧ ts ≤ t₁ :=
    ⟨min t₀ t₁, lt_min ht₀ ht₁, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨ρ₀, hρ₀, hball⟩ := GlobalTheory.T.iwasawa_factors_near_one_of_product_near_one n ε a j W hW ts hts
  obtain ⟨hdltm, -, hdlt⟩ := GlobalTheory.T.leviFactorInverseModulus_properties n ε a j W

  have hae : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.1 ∈ flagN ε W ∧ x.2.1 ∈ flagM ε W ∧ x.2.2 ∈ maxK ε := by
    have h1 : (μN.prod (μM.prod μK)) ((flagN ε W)ᶜ ×ˢ Set.univ) = 0 := by
      rw [Measure.prod_prod, hμN.1, zero_mul]
    have h2 : (μN.prod (μM.prod μK)) (Set.univ ×ˢ ((flagM ε W)ᶜ ×ˢ Set.univ)) = 0 := by
      rw [Measure.prod_prod, Measure.prod_prod, hμM.1, zero_mul, mul_zero]
    have h3 : (μN.prod (μM.prod μK)) (Set.univ ×ˢ (Set.univ ×ˢ (maxK ε)ᶜ)) = 0 := by
      rw [Measure.prod_prod, Measure.prod_prod, hμK.1, mul_zero, mul_zero]
    have e1 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.1 ∈ flagN ε W := by
      rw [ae_iff]
      exact measure_mono_null (fun x hx => Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩) h1
    have e2 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.2.1 ∈ flagM ε W := by
      rw [ae_iff]
      exact measure_mono_null
        (fun x hx => Set.mem_prod.2 ⟨Set.mem_univ _, Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩⟩) h2
    have e3 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.2.2 ∈ maxK ε := by
      rw [ae_iff]
      exact measure_mono_null
        (fun x hx => Set.mem_prod.2 ⟨Set.mem_univ _, Set.mem_prod.2 ⟨Set.mem_univ _, hx⟩⟩) h3
    filter_upwards [e1, e2, e3] with x hx1 hx2 hx3
    exact ⟨hx1, hx2, hx3⟩
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρρ₀ => ?_⟩
  have hPmeas : ∀ r : ℝ, Measurable fun x : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε × Formalism.REAL.UJ ε =>
      (hsBall ε r).indicator (1 : Formalism.REAL.UJ ε → ENNReal) (x.1 * x.2.1 * x.2.2) *
        (slab ε EL ρ r).indicator 1 x.2.2 := by
    intro r
    exact ((measurable_one.indicator (measurableSet_hsBall ε r)).comp
      ((measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd)).mul
      ((measurable_one.indicator (measurableSet_slab ε EL ρ r)).comp measurable_snd.snd)

  have hF : ∀ r : ℝ, (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) *
      (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) =
      ∫⁻ x, dlt j W x.2.1 * ((hsBall ε r).indicator 1 (x.1 * x.2.1 * x.2.2) *
        (slab ε EL ρ r).indicator 1 x.2.2) ∂(μN.prod (μM.prod μK)) := fun r =>
    GlobalTheory.IwConst.lintegral_triple_eq μN μM μK (dlt j W) hdltm _ (hPmeas r)
  have hc := continuous_nrm_uMat ε
  apply GlobalTheory.T.tendsto_small_ball_density_of_squeeze _ (dN + (dM + dK)) _ hvol
  intro η hη
  obtain ⟨t₂, ht₂, h₂⟩ := hCη η hη
  obtain ⟨t₃, ht₃, h₃⟩ := hdlt η hη
  obtain ⟨t, ht, htts, htρ, htt₂, htt₃⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ts ∧ t ≤ ρ ∧ t ≤ t₂ ∧ t ≤ t₃ :=
    ⟨min (min ts ρ) (min t₂ t₃), lt_min (lt_min hts hρ) (lt_min ht₂ ht₃),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hBmeas : ∀ s : ℝ, MeasurableSet {x : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε × Formalism.REAL.UJ ε |
      (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧
        gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ s} := by
    intro s
    refine measurableSet_setOfPred.2
      (((measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_fst) measurable_const)).and
      ((measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_snd.fst) measurable_const)).and
        (measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_snd.snd) measurable_const)))).and
      (measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const)))
    exact (continuous_gau EN EM EK EL).measurable.comp
      (((continuous_crd_uMat ε EN).measurable.comp measurable_fst).prodMk
        (((continuous_crd_uMat ε EM).measurable.comp measurable_snd.fst).prodMk
          ((continuous_crd_uMat ε EK).measurable.comp measurable_snd.snd)))
  refine ⟨fun s => (μN.prod (μM.prod μK)) {x |
      (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧
        gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ s},
    hasym t ht (htts.trans hts0), ?_⟩
  have hr₁ : 0 < min ρ₀ (t / (2 * C)) := lt_min hρ₀ (div_pos ht (by positivity))
  filter_upwards [Ioo_mem_nhdsGT hr₁] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hrρ₀ : r ≤ ρ₀ := (lt_of_lt_of_le hr1 (min_le_left _ _)).le
  have hrC : 2 * C * r < t := by
    have h := lt_of_lt_of_le hr1 (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    linarith
  have hη1 : (0 : ℝ) < 1 + η := by linarith
  rw [hF r]
  constructor
  ·
    rw [← lintegral_indicator_one (hBmeas _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with x hx
    obtain ⟨hxN, hxM, hxK⟩ := hx
    rw [Set.indicator_apply]
    split_ifs with hB
    · obtain ⟨⟨hu, hm, hk⟩, hγ⟩ := hB
      obtain ⟨-, hσγ, -, -, -⟩ := h₂ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu htt₂)
        (lt_of_lt_of_le hm htt₂) (lt_of_lt_of_le hk htt₂) _ _ rfl rfl
      have hσ : max (nrm (uMat (x.1 * x.2.1 * x.2.2) - 1)) (len (crd EL (uMat x.2.2 - 1))) ≤ r := by
        refine hσγ.trans ?_
        calc (1 + η) * gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
              crd EK (uMat x.2.2 - 1)) ≤ (1 + η) * (r / (1 + η)) :=
              mul_le_mul_of_nonneg_left hγ hη1.le
          _ = r := by field_simp
      have hmem1 : x.1 * x.2.1 * x.2.2 ∈ hsBall ε r :=
        ((le_max_left _ _).trans hσ : nrm (uMat (x.1 * x.2.1 * x.2.2) - 1) ≤ r)
      have hmem2 : x.2.2 ∈ slab ε EL ρ r :=
        (⟨lt_of_lt_of_le hk htρ, (le_max_right _ _).trans hσ⟩ :
          nrm (uMat x.2.2 - 1) < ρ ∧ len (crd EL (uMat x.2.2 - 1)) ≤ r)
      rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2]
      simp only [Pi.one_apply, mul_one]
      exact (h₃ x.2.1 hxM (lt_of_lt_of_le hm htt₃)).2
    · exact bot_le
  ·
    rw [← lintegral_indicator_one (hBmeas _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with x hx
    obtain ⟨hxN, hxM, hxK⟩ := hx
    by_cases hA : x.1 * x.2.1 * x.2.2 ∈ hsBall ε r
    swap
    · simp [Set.indicator_apply, hA]
    by_cases hS : x.2.2 ∈ slab ε EL ρ r
    swap
    · simp [Set.indicator_apply, hS]
    rw [Set.indicator_of_mem hA, Set.indicator_of_mem hS]
    simp only [Pi.one_apply, mul_one]
    have hA' : nrm (uMat (x.1 * x.2.1 * x.2.2) - 1) ≤ r := hA
    obtain ⟨hkρ, hL⟩ := (hS : nrm (uMat x.2.2 - 1) < ρ ∧ len (crd EL (uMat x.2.2 - 1)) ≤ r)
    obtain ⟨hu1, hm1, hk1⟩ :=
      hball x.1 hxN x.2.1 hxM x.2.2 (hA'.trans hrρ₀) (lt_of_lt_of_le hkρ hρρ₀)
    have hσ : max (nrm (uMat (x.1 * x.2.1 * x.2.2) - 1)) (len (crd EL (uMat x.2.2 - 1))) ≤ r :=
      max_le hA' hL
    obtain ⟨hγ1, -, hCu, hCm, hCk⟩ := h₁ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu1 hts1)
      (lt_of_lt_of_le hm1 hts1) (lt_of_lt_of_le hk1 hts1) _ _ rfl rfl
    have hγ2 : gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
        crd EK (uMat x.2.2 - 1)) ≤ 2 * r := by
      have := mul_le_mul_of_nonneg_left hσ (by norm_num : (0 : ℝ) ≤ 1 + 1)
      linarith
    have hCγ := mul_le_mul_of_nonneg_left hγ2 hC.le
    have hu : nrm (uMat x.1 - 1) < t := by linarith
    have hm : nrm (uMat x.2.1 - 1) < t := by linarith
    have hk : nrm (uMat x.2.2 - 1) < t := by linarith
    obtain ⟨hγη, -, -, -, -⟩ := h₂ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu htt₂)
      (lt_of_lt_of_le hm htt₂) (lt_of_lt_of_le hk htt₂) _ _ rfl rfl
    have hγ : gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
        crd EK (uMat x.2.2 - 1)) ≤ (1 + η) * r :=
      hγη.trans (mul_le_mul_of_nonneg_left hσ hη1.le)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [if_pos ⟨⟨hu, hm, hk⟩, hγ⟩, Pi.one_apply, mul_one]
    exact (h₃ x.2.1 hxM (lt_of_lt_of_le hm htt₃)).1

end GlobalTheory.IwConst
