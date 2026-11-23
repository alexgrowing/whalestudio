import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft

open MeasureTheory GlobalTheory.Grow GlobalTheory.Tw
open scoped ENNReal

namespace GlobalTheory.EvalAbs

theorem lintegral_eq_of_integral {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {m₁ : Measure α} {m₂ : Measure β} {a : α → γ} {b : β → γ} (ha : Measurable a) (hb : Measurable b)
    (h : ∀ f : γ → ℂ, Measurable f → (Integrable (fun x => f (a x)) m₁ ↔ Integrable (fun y => f (b y)) m₂) ∧
      (Integrable (fun y => f (b y)) m₂ → ∫ x, f (a x) ∂m₁ = ∫ y, f (b y) ∂m₂))
    (F : γ → ℝ≥0∞) (hF : Measurable F) : ∫⁻ x, F (a x) ∂m₁ = ∫⁻ y, F (b y) ∂m₂ := by
  have e : m₁.map a = m₂.map b := by
    ext A hA
    rw [Measure.map_apply ha hA, Measure.map_apply hb hA]
    obtain ⟨h1, h2⟩ := h (A.indicator fun _ => 1) (measurable_const.indicator hA)
    have e1 : (fun x => A.indicator (fun _ => (1 : ℂ)) (a x)) = (a ⁻¹' A).indicator fun _ => 1 := rfl
    have e2 : (fun x => A.indicator (fun _ => (1 : ℂ)) (b x)) = (b ⁻¹' A).indicator fun _ => 1 := rfl
    rw [e1, e2, integrable_indicator_iff (ha hA), integrable_indicator_iff (hb hA), integrableOn_const_iff,
      integrableOn_const_iff] at h1
    rw [e1, e2, integrable_indicator_iff (hb hA), integrableOn_const_iff, integral_indicator (ha hA),
      integral_indicator (hb hA)] at h2
    simp only [enorm_eq_zero, one_ne_zero, false_or, integral_const, MeasurableSet.univ, measureReal_restrict_apply,
      Set.univ_inter, Complex.real_smul, mul_one, Complex.ofReal_inj] at h1 h2
    by_cases hf : m₂ (b ⁻¹' A) < ∞
    · exact (ENNReal.toReal_eq_toReal_iff' (h1.2 hf).ne hf.ne).1 (h2 hf)
    · rw [not_lt_top_iff.1 hf, not_lt_top_iff.1 (fun h' => hf (h1.1 h'))]
  rw [← lintegral_map hF ha, e, lintegral_map hF hb]

theorem setLIntegral_mul_right {R : Type} [Group R] [MeasurableSpace R] [MeasurableMul R] {μ : Measure R}
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Γ : Subgroup R} [Countable Γ] {𝓡 : Set R}
    (h : IsFundamentalDomain Γ 𝓡 μ) (q : R → ℝ≥0∞) (hq : ∀ γ ∈ Γ, ∀ r, q (γ * r) = q r) (m : R) :
    ∫⁻ r in 𝓡, q (r * m) ∂μ = ∫⁻ r in 𝓡, q r ∂μ := by
  have hp : MeasurePreserving (· * m) μ μ := measurePreserving_mul_right μ m
  have h2 : IsFundamentalDomain Γ ((· * m) ⁻¹' 𝓡) μ :=
    h.preimage_of_equiv hp.quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  rw [h.setLIntegral_eq h2 (fun r => q (r * m)) fun γ r => by
    rw [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hq _ γ.2 _]
  exact hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.mulRight m).measurableEmbedding q 𝓡

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {R Γ : Subgroup G} {μR : Measure R} [μR.IsHaarMeasure] [μR.IsInvInvariant] {𝓡 : Set R} {𝓑 : Set G}

theorem exists_quotientIntegrable_of_le_mean (hΓR : Γ ≤ R) (hR : IsClosed (R : Set G)) [Countable Γ] [DiscreteTopology Γ]
    (h𝓡 : IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR) (h𝓑 : IsFundamentalDomain Γ 𝓑 μ) {K : G → ℝ≥0∞}
    (hK : Measurable K) (hKΓ : ∀ γ ∈ Γ, ∀ g, K (γ * g) = K g) (hfin : ∫⁻ g in 𝓑, K g ∂μ < ∞) {f : G → ℂ}
    (hf : Measurable f) (hfR : ∀ r ∈ R, ∀ g, f (r * g) = f g) (hle : ∀ h, ‖f h‖ₑ ≤ ∫⁻ r in 𝓡, K (r * h) ∂μR) :
    ∃ z, IsQuotIntL1 μR μ f z := by
  refine ⟨_, (isQuotIntL1_iff hR hf).2 ⟨hfR, ⟨(measurable_comp_out hf hfR).aestronglyMeasurable, ?_⟩, rfl⟩⟩
  obtain ⟨S, hSm, hS⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hSfd : IsFundamentalDomain Γ S μ := IsFundamentalDomain.mk' hSm.nullMeasurableSet hS
  have hSh : ∀ h : G, MeasurableSet {r : R | (r : G) * h ∈ S} := fun h =>
    (continuous_subtype_val.mul continuous_const).measurable hSm
  have e : ∀ h : G, ∫⁻ r in 𝓡, K (r * h) ∂μR = ∫⁻ r : R, S.indicator K (r * h) ∂μR := fun h => by
    have hfd : IsFundamentalDomain (Γ.subgroupOf R) {r : R | (r : G) * h ∈ S} μR :=
      IsFundamentalDomain.mk' (hSh h).nullMeasurableSet (GlobalTheory.QuotDiscrete.existsUnique_subgroupOf hΓR hS h)
    rw [h𝓡.setLIntegral_eq hfd (fun r : R => K (r * h)) fun γ r => by
      change K ((((γ : R) : G) * r) * h) = _
      rw [mul_assoc]; exact hKΓ _ γ.2 _, ← lintegral_indicator (hSh h)]
    rfl
  calc ∫⁻ c, ‖f (Quotient.out c)‖ₑ ∂quotMeas R μ μR
      ≤ ∫⁻ c, ∫⁻ r : R, S.indicator K (r * Quotient.out c) ∂μR ∂quotMeas R μ μR :=
        lintegral_mono fun c => (hle _).trans (e _).le
    _ = ∫⁻ g, S.indicator K g ∂μ := (isQuotMeasure_quotMeas hR _ (hK.indicator hSm)).symm
    _ = ∫⁻ g in 𝓑, K g ∂μ := by
        rw [lintegral_indicator hSm]
        exact hSfd.setLIntegral_eq h𝓑 K fun γ x => hKΓ _ γ.2 x
    _ < ∞ := hfin

theorem exists_quotientIntegrable_fold_unimodular (hΓR : Γ ≤ R) (hR : IsClosed (R : Set G)) [Countable Γ] [DiscreteTopology Γ]
    (h𝓡 : IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR) (h𝓑 : IsFundamentalDomain Γ 𝓑 μ)
    {U : Type} [Group U] [MeasurableSpace U] [MeasurableMul U] [MeasurableInv U] {ν : Measure U} [SFinite ν]
    [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (j : U →* G) (hj : Measurable j) (hjR : ∀ u, j u ∈ R)
    {q : G → G → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (hqΓ : ∀ γ ∈ Γ, ∀ g, ∀ r ∈ R, q (γ * g) (γ * r) = q g r)
    (hqR : ∀ r ∈ R, ∃ v, ∀ g u, q g (r * j u) = q g (j (v * u)))
    (hfin : ∫⁻ g in 𝓑, ∫⁻ u, q g (j u) ∂ν ∂μ < ∞) {P : G → ℂ} (hP : Measurable P)
    (hPR : ∀ r ∈ R, ∃ v, ∀ g u, P (j u * (r * g)) = P (j (u * v) * g))
    (hle : ∀ h, ‖P h‖ₑ ≤ ∫⁻ r in 𝓡, q (r * h) r ∂μR) :
    ∃ z, IsQuotIntL1 μR μ (fun h => ((∫ u, ‖P (j u * h)‖ ∂ν : ℝ) : ℂ)) z := by
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  have : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  have : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  have : ν.IsMulRightInvariant := by rw [← Measure.inv_eq_self ν]; infer_instance
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hU : ∀ r ∈ R, ∀ g, ∫⁻ u, q g (r * j u) ∂ν = ∫⁻ u, q g (j u) ∂ν := fun r hr g => by
    obtain ⟨v, hv⟩ := hqR r hr
    simp only [hv]
    exact lintegral_mul_left_eq_self (fun u => q g (j u)) v
  refine exists_quotientIntegrable_of_le_mean hΓR hR h𝓡 h𝓑 (K := fun g => ∫⁻ u, q g (j u) ∂ν) ?_ (fun γ hγ g => ?_) hfin ?_
    (fun r hr g => ?_) fun h => ?_
  · exact (hq.comp (measurable_fst.prodMk (hj.comp measurable_snd))).lintegral_prod_right'
  · rw [← hU γ⁻¹ (inv_mem (hΓR hγ)) g]
    refine lintegral_congr fun u => ?_
    rw [← hqΓ γ hγ g _ (mul_mem (inv_mem (hΓR hγ)) (hjR u)), mul_inv_cancel_left]
  · refine Complex.measurable_ofReal.comp (StronglyMeasurable.measurable ?_)
    exact (hP.comp ((hj.comp measurable_snd).mul measurable_fst)).norm.stronglyMeasurable.integral_prod_right'
  · obtain ⟨v, hv⟩ := hPR r hr
    simp only [hv]
    rw [integral_mul_right_eq_self (fun u => ‖P (j u * g)‖) v]
  · have hm : Measurable fun p : U × R => q (p.2 * h) (p.2 * j p.1⁻¹) :=
      hq.comp (((measurable_subtype_coe.comp measurable_snd).mul_const h).prodMk
        ((measurable_subtype_coe.comp measurable_snd).mul (hj.comp measurable_fst.inv)))
    calc ‖((∫ u, ‖P (j u * h)‖ ∂ν : ℝ) : ℂ)‖ₑ = ‖∫ u, ‖P (j u * h)‖ ∂ν‖ₑ := by
          simp only [enorm, Complex.nnnorm_real]
      _ ≤ ∫⁻ u, ‖‖P (j u * h)‖‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ u, ∫⁻ r in 𝓡, q (r * h) (r * j u⁻¹) ∂μR ∂ν := by
          refine lintegral_mono fun u => ?_
          rw [enorm_norm]
          refine (hle _).trans (le_of_eq ?_)
          rw [← setLIntegral_mul_right h𝓡 (fun r : R => q (r * h) (r * j u⁻¹)) (fun γ hγ r => by
            simp only [Subgroup.coe_mul, mul_assoc]
            exact hqΓ _ hγ _ _ (mul_mem r.2 (hjR _))) ⟨j u, hjR u⟩]
          simp only [Subgroup.coe_mul, mul_assoc, map_inv, mul_inv_cancel, mul_one]
      _ = ∫⁻ r in 𝓡, ∫⁻ u, q (r * h) (r * j u⁻¹) ∂ν ∂μR := lintegral_lintegral_swap hm.aemeasurable
      _ = _ := by
          refine lintegral_congr fun r => ?_
          rw [lintegral_inv_eq_self (μ := ν) fun u => q (r * h) (r * j u), hU r r.2]

end

end GlobalTheory.EvalAbs
