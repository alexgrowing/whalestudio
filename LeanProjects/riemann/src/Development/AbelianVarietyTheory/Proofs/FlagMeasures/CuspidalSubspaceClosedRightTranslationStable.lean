import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AestronglyMeasurableCompRep

open MeasureTheory Filter Set
open scoped ENNReal Topology Pointwise

namespace GlobalTheory.CuspSubspace

open GlobalTheory.RightRegFund

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ]

theorem qmp_mul (ν : Measure G) [SFinite ν] :
    Measure.QuasiMeasurePreserving (fun p : G × G => p.2 * p.1) (μ.prod ν) μ := by
  have hm : Measurable (fun p : G × G => p.2 * p.1) := measurable_snd.mul measurable_fst
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hm hs)]
  have h1 : ∀ y : G, μ ((fun x => (x, y)) ⁻¹' ((fun p : G × G => p.2 * p.1) ⁻¹' s)) = 0 := by
    intro y
    change μ ((fun x => y * x) ⁻¹' s) = 0
    rw [measure_preimage_mul]
    exact h0
  simp only [h1, lintegral_zero]

theorem ae_ae_mul (ν : Measure G) [SFinite ν] {p : G → Prop} (hp : ∀ᵐ y ∂μ, p y) :
    ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, p (m * x) := by
  have h := (qmp_mul (μ := μ) ν).ae hp
  exact Measure.ae_ae_of_ae_prod (p := fun q : G × G => p (q.2 * q.1)) h

theorem constTerm_congr (ν : Measure G) [SFinite ν] {f g : G → ℂ} (h : f =ᵐ[μ] g) :
    ∀ᵐ x ∂μ, ∫ m, f (m * x) ∂ν = ∫ m, g (m * x) ∂ν := by
  filter_upwards [ae_ae_mul (μ := μ) ν (p := fun y => f y = g y) h] with x hx
  exact integral_congr_ae hx

variable {Γ : Subgroup G} [Countable Γ] {D : Set G} {r : G → G}

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [Countable Γ] in
theorem exists_mult_bound {C : Set G} (hC : ((C * C⁻¹) ∩ (Γ : Set G)).Finite) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x : G, ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) ≤ M := by
  classical
  set S : Set Γ := {δ | (δ : G) ∈ (C * C⁻¹) ∩ (Γ : Set G)} with hS
  have hSf : S.Finite := hC.preimage Subtype.coe_injective.injOn
  refine ⟨(hSf.toFinset.card : ℝ≥0∞), ENNReal.natCast_ne_top _, fun x => ?_⟩
  by_cases hx : ∃ γ₀ : Γ, (γ₀ : G) * x ∈ C
  · obtain ⟨γ₀, hγ₀⟩ := hx
    calc ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)
        ≤ ∑' γ : Γ, S.indicator (fun _ => (1 : ℝ≥0∞)) (γ * γ₀⁻¹) := by
          refine ENNReal.tsum_le_tsum fun γ => ?_
          by_cases hγ : (γ : G) * x ∈ C
          · have hmem : γ * γ₀⁻¹ ∈ S := by
              refine ⟨?_, (γ * γ₀⁻¹).2⟩
              refine Set.mem_mul.2 ⟨(γ : G) * x, hγ, ((γ₀ : G) * x)⁻¹, Set.inv_mem_inv.2 hγ₀, ?_⟩
              simp [mul_assoc]
            rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hmem]
          · rw [Set.indicator_of_notMem hγ]
            exact zero_le
      _ = ∑' δ : Γ, S.indicator (fun _ => (1 : ℝ≥0∞)) δ :=
          (Equiv.mulRight γ₀⁻¹).tsum_eq (fun δ => S.indicator (fun _ => (1 : ℝ≥0∞)) δ)
      _ = hSf.toFinset.card := by
          rw [tsum_eq_sum (s := hSf.toFinset) fun b hb => Set.indicator_of_notMem (by simpa using hb) _]
          rw [Finset.sum_congr rfl fun b hb => Set.indicator_of_mem (by simpa using hb) _]
          simp
  · simp only [not_exists] at hx
    simp [Set.indicator_of_notMem (hx _)]

omit [SecondCountableTopology G] [SFinite μ] in
theorem setLIntegral_rep_le (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {C : Set G} (hCm : MeasurableSet C)
    {M : ℝ≥0∞} (hM : ∀ x : G, ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) ≤ M)
    {φ : G → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y in C, φ (r y) ∂μ ≤ M * ∫⁻ x in D, φ x ∂μ := by
  classical
  have hgood : ∀ᵐ x ∂(μ.restrict D), x ∈ D ∧ Good Γ D x :=
    (ae_restrict_mem hDm).and (ae_restrict_of_ae (GlobalTheory.RightRegFund.ae_good hD))
  have hr1 : ∀ x, x ∈ D → Good Γ D x → ∀ γ : Γ, r ((γ : G) * x) = x := by
    intro x hxD hx γ
    rw [GlobalTheory.RightRegFund.rep_mul hr hx γ]
    have h1 := GlobalTheory.RightRegFund.rep_eq hr hx (γ := 1) (by simpa using hxD)
    simpa using h1
  calc ∫⁻ y in C, φ (r y) ∂μ = ∫⁻ y, C.indicator (fun y => φ (r y)) y ∂μ :=
        (lintegral_indicator hCm _).symm
    _ = ∑' γ : Γ, ∫⁻ x in D, C.indicator (fun y => φ (r y)) (γ • x) ∂μ := hD.lintegral_eq_tsum'' _
    _ = ∑' γ : Γ, ∫⁻ x in D, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x ∂μ := by
        refine tsum_congr fun γ => lintegral_congr_ae ?_
        filter_upwards [hgood] with x hx
        change C.indicator (fun y => φ (r y)) ((γ : G) * x) = _
        by_cases hc : (γ : G) * x ∈ C
        · rw [Set.indicator_of_mem hc, Set.indicator_of_mem hc, hr1 x hx.1 hx.2 γ, one_mul]
        · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc, zero_mul]
    _ = ∫⁻ x in D, ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x ∂μ := by
        refine (lintegral_tsum fun γ : Γ => ?_).symm
        exact (((measurable_const.indicator hCm).comp (measurable_const_mul (γ : G))).mul hφ).aemeasurable
    _ = ∫⁻ x in D, (∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) * φ x ∂μ := by
        simp_rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ x in D, M * φ x ∂μ := lintegral_mono fun x => by gcongr; exact hM x
    _ = M * ∫⁻ x in D, φ x ∂μ := lintegral_const_mul M hφ

omit [SecondCountableTopology G] [SFinite μ] in
theorem exists_L1_bound_of_L2_section [T2Space G] [IsFiniteMeasureOnCompacts μ]
    (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hΓ : ∀ C : Set G, IsCompact C → (C ∩ (Γ : Set G)).Finite) {C : Set G} (hC : IsCompact C) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ F : Lp ℂ 2 (μ.restrict D), ∫⁻ y in C, ‖F (r y)‖ₑ ∂μ ≤ K * ‖F‖ₑ := by
  obtain ⟨M, hMt, hM⟩ := exists_mult_bound (Γ := Γ) (hΓ _ (hC.mul hC.inv))
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  refine ⟨M ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ),
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hMt)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC.measure_lt_top.ne), fun F => ?_⟩
  have hFm : StronglyMeasurable (F : G → ℂ) := Lp.stronglyMeasurable F
  have hFr : AEStronglyMeasurable (fun y => F (r y)) (μ.restrict C) :=
    (GlobalTheory.RightRegFund.aestronglyMeasurable_comp_rep hD hDm hr hFm).restrict
  have h2 : ∫⁻ y in C, ‖F (r y)‖ₑ ^ (2 : ℝ) ∂μ ≤ M * ∫⁻ x in D, ‖F x‖ₑ ^ (2 : ℝ) ∂μ :=
    setLIntegral_rep_le hD hDm hr hCm hM (hFm.measurable.enorm.pow_const _)
  have hF : ‖F‖ₑ = (∫⁻ x in D, ‖F x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hFr
  rw [eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    Measure.restrict_apply_univ] at h1
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_one] at h1
  rw [show (1 : ℝ) / 1 - 1 / 2 = 1 / 2 by norm_num] at h1
  calc ∫⁻ y in C, ‖F (r y)‖ₑ ∂μ
      ≤ (∫⁻ y in C, ‖F (r y)‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ) := h1
    _ ≤ (M * ∫⁻ x in D, ‖F x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ) := by gcongr
    _ = M ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ) * ‖F‖ₑ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hF]
        ring

theorem aesm_prod (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) (ν : Measure G) [SFinite ν]
    (F : Lp ℂ 2 (μ.restrict D)) :
    AEStronglyMeasurable (fun p : G × G => F (r (p.2 * p.1))) (μ.prod ν) := by
  exact (GlobalTheory.RightRegFund.aestronglyMeasurable_comp_rep hD hDm hr
    (Lp.stronglyMeasurable F)).comp_quasiMeasurePreserving (qmp_mul ν)

theorem exists_double_bound [T2Space G] [IsFiniteMeasureOnCompacts μ]
    (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hΓ : ∀ C : Set G, IsCompact C → (C ∩ (Γ : Set G)).Finite)
    {ν : Measure G} [IsFiniteMeasure ν] {C : Set G} (hC : IsCompact C)
    (hν : ∀ᵐ m ∂ν, ∃ γ : Γ, (γ : G)⁻¹ * m ∈ C) {B : Set G} (hB : IsCompact B) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ F : Lp ℂ 2 (μ.restrict D),
      ∫⁻ x in B, ∫⁻ m, ‖F (r (m * x))‖ₑ ∂ν ∂μ ≤ K * ‖F‖ₑ := by
  obtain ⟨K, hKt, hK⟩ := exists_L1_bound_of_L2_section hD hDm hr hΓ (hC.mul hB)
  refine ⟨ν Set.univ * K, ENNReal.mul_ne_top (measure_ne_top ν _) hKt, fun F => ?_⟩
  have hBm : MeasurableSet B := hB.isClosed.measurableSet
  have hCBm : MeasurableSet (C * B) := (hC.mul hB).isClosed.measurableSet
  have e : (μ.restrict B).prod ν = (μ.prod ν).restrict (B ×ˢ Set.univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : AEMeasurable (Function.uncurry fun x m => ‖F (r (m * x))‖ₑ) ((μ.restrict B).prod ν) := by
    rw [e]
    exact (aesm_prod hD hDm hr ν F).enorm.restrict
  rw [lintegral_lintegral_swap hmeas]
  calc ∫⁻ m, ∫⁻ x in B, ‖F (r (m * x))‖ₑ ∂μ ∂ν ≤ ∫⁻ _m, K * ‖F‖ₑ ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hν] with m hm
        obtain ⟨γ, hγ⟩ := hm
        obtain ⟨c, hcC, rfl⟩ : ∃ c ∈ C, m = (γ : G) * c := ⟨(γ : G)⁻¹ * m, hγ, by simp⟩
        have hgood : ∀ᵐ x ∂μ, Good Γ D (c * x) :=
          (measurePreserving_mul_left μ c).quasiMeasurePreserving.ae (GlobalTheory.RightRegFund.ae_good hD)
        calc ∫⁻ x in B, ‖F (r ((γ : G) * c * x))‖ₑ ∂μ = ∫⁻ x in B, ‖F (r (c * x))‖ₑ ∂μ := by
              refine lintegral_congr_ae (ae_restrict_of_ae ?_)
              filter_upwards [hgood] with x hx
              rw [mul_assoc, GlobalTheory.RightRegFund.rep_mul hr hx γ]
          _ = ∫⁻ x, B.indicator (fun x => ‖F (r (c * x))‖ₑ) x ∂μ := (lintegral_indicator hBm _).symm
          _ ≤ ∫⁻ x, (C * B).indicator (fun y => ‖F (r y)‖ₑ) (c * x) ∂μ := by
              refine lintegral_mono fun x => ?_
              by_cases hx : x ∈ B
              · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mul_mem_mul hcC hx)]
              · rw [Set.indicator_of_notMem hx]
                exact zero_le
          _ = ∫⁻ y, (C * B).indicator (fun y => ‖F (r y)‖ₑ) y ∂μ :=
              lintegral_mul_left_eq_self _ c
          _ = ∫⁻ y in C * B, ‖F (r y)‖ₑ ∂μ := lintegral_indicator hCBm _
          _ ≤ K * ‖F‖ₑ := hK F
    _ = ν Set.univ * K * ‖F‖ₑ := by
        rw [lintegral_const]
        ring

omit [Group G] [IsTopologicalGroup G] [BorelSpace G] [μ.IsMulLeftInvariant] [SFinite μ] in
theorem ae_of_compact [LocallyCompactSpace G] {p : G → Prop}
    (h : ∀ B : Set G, IsCompact B → ∀ᵐ x ∂(μ.restrict B), p x) : ∀ᵐ x ∂μ, p x := by
  have h2 : ∀ n, ∀ᵐ x ∂(μ.restrict (compactCovering G n)), p x :=
    fun n => h _ (isCompact_compactCovering G n)
  have h3 := (ae_restrict_iUnion_iff (μ := μ) (compactCovering G) p).2 h2
  rwa [iUnion_compactCovering, Measure.restrict_univ] at h3

variable [T2Space G] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ]

theorem ae_integrable (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hΓ : ∀ C : Set G, IsCompact C → (C ∩ (Γ : Set G)).Finite)
    {ν : Measure G} [IsFiniteMeasure ν] {C : Set G} (hC : IsCompact C)
    (hν : ∀ᵐ m ∂ν, ∃ γ : Γ, (γ : G)⁻¹ * m ∈ C) (F : Lp ℂ 2 (μ.restrict D)) :
    ∀ᵐ x ∂μ, Integrable (fun m => F (r (m * x))) ν := by
  refine ae_of_compact (μ := μ) fun B hB => ?_
  obtain ⟨K, hKt, hK⟩ := exists_double_bound hD hDm hr hΓ hC hν hB
  have e : (μ.restrict B).prod ν = (μ.prod ν).restrict (B ×ˢ Set.univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hprod : AEStronglyMeasurable (fun p : G × G => F (r (p.2 * p.1))) ((μ.restrict B).prod ν) := by
    rw [e]
    exact (aesm_prod hD hDm hr ν F).restrict
  have hfin : ∫⁻ x in B, ∫⁻ m, ‖F (r (m * x))‖ₑ ∂ν ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hKt enorm_ne_top) (hK F)
  filter_upwards [hprod.prodMk_left, ae_lt_top' hprod.enorm.lintegral_prod_right' hfin] with x h1 h2
  exact ⟨h1, h2⟩

theorem constTerm_add (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hΓ : ∀ C : Set G, IsCompact C → (C ∩ (Γ : Set G)).Finite)
    {ν : Measure G} [IsFiniteMeasure ν] {C : Set G} (hC : IsCompact C)
    (hν : ∀ᵐ m ∂ν, ∃ γ : Γ, (γ : G)⁻¹ * m ∈ C) (F F' : Lp ℂ 2 (μ.restrict D)) :
    ∀ᵐ x ∂μ, ∫ m, (F + F') (r (m * x)) ∂ν = ∫ m, F (r (m * x)) ∂ν + ∫ m, F' (r (m * x)) ∂ν := by
  have h1 : ∀ᵐ y ∂μ, (F + F') (r y) = F (r y) + F' (r y) := by
    filter_upwards [GlobalTheory.RightRegFund.ae_rep (μ := μ) hDm hr (Lp.coeFn_add F F')] with y hy
    simpa using hy
  filter_upwards [ae_ae_mul (μ := μ) ν h1, ae_integrable hD hDm hr hΓ hC hν F,
    ae_integrable hD hDm hr hΓ hC hν F'] with x hx hFx hF'x
  rw [integral_congr_ae hx, integral_add hFx hF'x]

theorem isClosed_constTerm_zero (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hΓ : ∀ C : Set G, IsCompact C → (C ∩ (Γ : Set G)).Finite)
    {ν : Measure G} [IsFiniteMeasure ν] {C : Set G} (hC : IsCompact C)
    (hν : ∀ᵐ m ∂ν, ∃ γ : Γ, (γ : G)⁻¹ * m ∈ C) :
    IsClosed {F : Lp ℂ 2 (μ.restrict D) | ∀ᵐ x ∂μ, ∫ m, F (r (m * x)) ∂ν = 0} := by
  refine isClosed_of_closure_subset fun F hF => ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hF
  change ∀ᵐ x ∂μ, ∫ m, F (r (m * x)) ∂ν = 0
  refine ae_of_compact (μ := μ) fun B hB => ?_
  obtain ⟨K, hKt, hK⟩ := exists_double_bound hD hDm hr hΓ hC hν hB
  have e : (μ.restrict B).prod ν = (μ.prod ν).restrict (B ×ˢ Set.univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : AEStronglyMeasurable (fun x => ∫ m, F (r (m * x)) ∂ν) (μ.restrict B) := by
    have h : AEStronglyMeasurable (fun p : G × G => F (r (p.2 * p.1))) ((μ.restrict B).prod ν) := by
      rw [e]
      exact (aesm_prod hD hDm hr ν F).restrict
    exact h.integral_prod_right'
  have hle : ∀ n, ∫⁻ x in B, ‖∫ m, F (r (m * x)) ∂ν‖ₑ ∂μ ≤ K * ‖F - u n‖ₑ := by
    intro n
    refine le_trans (lintegral_mono_ae ?_) (hK (F - u n))
    have h0 : ∀ᵐ x ∂μ, ∫ m, (u n) (r (m * x)) ∂ν = 0 := hu n
    filter_upwards [ae_restrict_of_ae h0,
      ae_restrict_of_ae (constTerm_add hD hDm hr hΓ hC hν (F - u n) (u n))] with x hx0 hxa
    rw [sub_add_cancel] at hxa
    rw [hxa, hx0, add_zero]
    exact enorm_integral_le_lintegral_enorm _
  have hlim' : Tendsto (fun n => K * ‖F - u n‖ₑ) atTop (𝓝 (K * 0)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr hKt)
    have h1 : Tendsto (fun n => ‖u n - F‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hlim
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_zero] at h2
    refine h2.congr fun n => ?_
    rw [norm_sub_rev, ofReal_norm]
  rw [mul_zero] at hlim'
  have hzero : ∫⁻ x in B, ‖∫ m, F (r (m * x)) ∂ν‖ₑ ∂μ = 0 :=
    le_antisymm (ge_of_tendsto' hlim' hle) zero_le
  rw [lintegral_eq_zero_iff' hmeas.enorm] at hzero
  filter_upwards [hzero] with x hx
  simpa using hx

end General

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

theorem cuspidal_closed_stable : ∀ B : RowsAut, ∃ S : Submodule ℂ (B.I.L2 B.μf B.fund), (∀ F, F ∈ S ↔ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext F)) ∧ IsClosed (S : Set (B.I.L2 B.μf B.fund)) ∧ (∀ g, ∀ F ∈ S, B.R g F ∈ S) ∧ ∀ (F : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), (∀ γ ∈ B.I.GFset, ∀ y, f (γ * y) = f y) → Continuous f → f =ᵐ[B.I.muA B.μf] B.I.ext F → (F ∈ S ↔ B.I.IsCuspFn (B.I.muA B.μf) f) := by
  intro B
  classical
  obtain ⟨hT2, hLC, hSC, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨Γ, hΓset, hΓc, hΓfin, hΓfd⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain B.I
  have h8 := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨h8.1⟩
  have : (B.I.muA B.μf).IsMulRightInvariant := ⟨h8.2.1⟩
  have : SFinite (B.I.muA B.μf) := by
    unfold Formalism.MainNotions.S.AutInst.muA
    infer_instance
  have : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold Formalism.MainNotions.S.AutInst.muA
    infer_instance
  have hD : IsFundamentalDomain Γ B.fund (B.I.muA B.μf) := hΓfd B.μf B.fund B.fund_spec
  have hDm : MeasurableSet B.fund := B.fund_spec.1
  have hfin : ∀ C : Set B.I.GA, IsCompact C → (C ∩ (Γ : Set B.I.GA)).Finite := by
    intro C hC
    rw [hΓset]
    exact hΓfin C hC
  have hr : ∀ y, ∃ γ : Γ, B.I.rep B.fund y = (γ : B.I.GA) * y ∧ B.I.rep B.fund y ∈ B.fund := by
    intro y
    have hex : ∃ γ ∈ B.I.GFset, γ * y ∈ B.fund := B.fund_spec.2.1 y
    have hrep : B.I.rep B.fund y = hex.choose * y := by
      unfold Formalism.MainNotions.S.AutInst.rep
      rw [dif_pos hex]
    have hmem : hex.choose ∈ Γ := by
      rw [← SetLike.mem_coe, hΓset]
      exact hex.choose_spec.1
    exact ⟨⟨hex.choose, hmem⟩, hrep, hrep ▸ hex.choose_spec.2⟩
  have hν : ∀ W : Submodule B.I.E (Fin B.I.n → B.I.E), B.I.IsIsot W → ∀ ν : Measure B.I.GA,
      B.I.IsNQuotMeas W ν → ∃ Cp : Set B.I.GA, IsCompact Cp ∧
        ∀ᵐ m ∂ν, ∃ γ : Γ, (γ : B.I.GA)⁻¹ * m ∈ Cp := by
    intro W hW ν hνW
    obtain ⟨-, -, -, -, Cp, hCp, -, hCpm⟩ := GlobalTheory.T.strong_approximation_unitaryUnipotentRadical B.I W hW
    refine ⟨Cp, hCp, ?_⟩
    have hN : ∀ᵐ m ∂ν, m ∈ B.I.NA W := ae_iff.2 hνW.2.2.1
    filter_upwards [hN] with m hm
    obtain ⟨γ, hγ, hγm⟩ := hCpm m hm
    have hγΓ : γ ∈ Γ := by
      rw [← SetLike.mem_coe, hΓset]
      exact hγ.1
    exact ⟨⟨γ, hγΓ⟩, hγm⟩
  have hzero : ∀ (ν : Measure B.I.GA) [IsFiniteMeasure ν],
      ∀ᵐ x ∂(B.I.muA B.μf), ∫ m, B.I.ext (0 : B.I.L2 B.μf B.fund) (m * x) ∂ν = 0 := by
    intro ν _
    have h1 : ∀ᵐ y ∂(B.I.muA B.μf), (0 : B.I.L2 B.μf B.fund) (B.I.rep B.fund y) = 0 := by
      filter_upwards [GlobalTheory.RightRegFund.ae_rep (μ := B.I.muA B.μf) hDm hr
        (Lp.coeFn_zero ℂ 2 ((B.I.muA B.μf).restrict B.fund))] with y hy
      simpa using hy
    filter_upwards [ae_ae_mul (μ := B.I.muA B.μf) ν h1] with x hx
    change ∫ m, (0 : B.I.L2 B.μf B.fund) (B.I.rep B.fund (m * x)) ∂ν = 0
    rw [integral_congr_ae hx]
    simp
  have hsmul : ∀ (ν : Measure B.I.GA) [IsFiniteMeasure ν] (c : ℂ) (F : B.I.L2 B.μf B.fund),
      ∀ᵐ x ∂(B.I.muA B.μf), ∫ m, B.I.ext (c • F) (m * x) ∂ν = c * ∫ m, B.I.ext F (m * x) ∂ν := by
    intro ν _ c F
    have h1 : ∀ᵐ y ∂(B.I.muA B.μf), (c • F) (B.I.rep B.fund y) = c * F (B.I.rep B.fund y) := by
      filter_upwards [GlobalTheory.RightRegFund.ae_rep (μ := B.I.muA B.μf) hDm hr (Lp.coeFn_smul c F)] with y hy
      simpa using hy
    filter_upwards [ae_ae_mul (μ := B.I.muA B.μf) ν h1] with x hx
    change ∫ m, (c • F) (B.I.rep B.fund (m * x)) ∂ν = c * ∫ m, F (B.I.rep B.fund (m * x)) ∂ν
    rw [integral_congr_ae hx, integral_const_mul]
  let S : Submodule ℂ (B.I.L2 B.μf B.fund) :=
    { carrier := {F | B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext F)}
      add_mem' := by
        intro F F' hF hF' W hW ν hνW
        have := hνW.1
        obtain ⟨Cp, hCp, hCpm⟩ := hν W hW ν hνW
        filter_upwards [constTerm_add (μ := B.I.muA B.μf) hD hDm hr hfin hCp hCpm F F',
          hF W hW ν hνW, hF' W hW ν hνW] with x h1 h2 h3
        change ∫ m, (F + F') (B.I.rep B.fund (m * x)) ∂ν = 0
        rw [h1]
        change ∫ m, B.I.ext F (m * x) ∂ν + ∫ m, B.I.ext F' (m * x) ∂ν = 0
        rw [h2, h3, add_zero]
      zero_mem' := by
        intro W hW ν hνW
        have := hνW.1
        exact hzero ν
      smul_mem' := by
        intro c F hF W hW ν hνW
        have := hνW.1
        filter_upwards [hsmul ν c F, hF W hW ν hνW] with x h1 h2
        rw [h1, h2, mul_zero] }
  refine ⟨S, fun F => Iff.rfl, ?_, ?_, ?_⟩
  · change IsClosed {F : B.I.L2 B.μf B.fund | ∀ W : Submodule B.I.E (Fin B.I.n → B.I.E), B.I.IsIsot W →
      ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ᵐ x ∂(B.I.muA B.μf), ∫ m, B.I.ext F (m * x) ∂ν = 0}
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun W => isClosed_iInter fun hW => isClosed_iInter fun ν =>
      isClosed_iInter fun hνW => ?_
    have := hνW.1
    obtain ⟨Cp, hCp, hCpm⟩ := hν W hW ν hνW
    exact isClosed_constTerm_zero (μ := B.I.muA B.μf) hD hDm hr hfin hCp hCpm
  · intro g F hF W hW ν hνW
    have := hνW.1
    have h1 : ∀ᵐ y ∂(B.I.muA B.μf), B.I.ext (B.R g F) y = B.I.ext F (y * g) := by
      filter_upwards [GlobalTheory.RightRegFund.ae_rep (μ := B.I.muA B.μf) hDm hr (B.R_spec g F),
        GlobalTheory.RightRegFund.ae_good_mul hD g] with y hy hg
      change (B.R g F) (B.I.rep B.fund y) = F (B.I.rep B.fund (y * g))
      rw [hy]
      obtain ⟨γ, hγ, -⟩ := hr y
      change F (B.I.rep B.fund (B.I.rep B.fund y * g)) = F (B.I.rep B.fund (y * g))
      rw [hγ, mul_assoc, GlobalTheory.RightRegFund.rep_mul hr hg γ]
    have h2 : ∀ᵐ x ∂(B.I.muA B.μf), ∫ m, B.I.ext F (m * (x * g)) ∂ν = 0 :=
      (measurePreserving_mul_right (B.I.muA B.μf) g).quasiMeasurePreserving.ae (hF W hW ν hνW)
    filter_upwards [ae_ae_mul (μ := B.I.muA B.μf) ν h1, h2] with x hx h2x
    rw [integral_congr_ae hx]
    simpa [mul_assoc] using h2x
  · intro F f _ _ hf
    change B.I.IsCuspFn _ (B.I.ext F) ↔ B.I.IsCuspFn _ f
    refine forall_congr' fun W => forall_congr' fun hW => forall_congr' fun ν =>
      forall_congr' fun hνW => ?_
    have := hνW.1
    have h := constTerm_congr (μ := B.I.muA B.μf) ν hf
    constructor
    · intro h0
      filter_upwards [h0, h] with x h1 h2
      rw [h2]
      exact h1
    · intro h0
      filter_upwards [h0, h] with x h1 h2
      rw [← h2]
      exact h1

end GlobalTheory.CuspSubspace
