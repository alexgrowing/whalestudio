import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopologyStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AestronglyMeasurableCompRep

open MeasureTheory Filter Set Formalism.MainNotions.S GlobalTheory.RightRegFund
open scoped ENNReal Pointwise

namespace GlobalTheory.LocalL2Isometry

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ]
  {D : Set G} {r : G → G}

private lemma card_le_of_translates_mem_mul_inv_tsum_indicator {C : Set G} (S : Finset Γ)
    (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) (x : G) :
    ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) ≤ S.card := by
  classical
  by_cases h : ∃ γ₀ : Γ, (γ₀ : G) * x ∈ C
  · obtain ⟨γ₀, h₀⟩ := h
    have hsupp : ∀ γ ∉ S.image (· * γ₀),
        C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) = 0 := by
      intro γ hγ
      by_contra hne
      have hγC : (γ : G) * x ∈ C := by
        by_contra hn
        exact hne (Set.indicator_of_notMem hn _)
      apply hγ
      refine Finset.mem_image.2 ⟨γ * γ₀⁻¹, hS _ ?_, by simp⟩
      refine Set.mem_mul.2 ⟨(γ : G) * x, hγC, ((γ₀ : G) * x)⁻¹, by simpa using h₀, ?_⟩
      simp [mul_assoc]
    rw [tsum_eq_sum hsupp]
    calc ∑ γ ∈ S.image (· * γ₀), C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)
        ≤ ∑ _γ ∈ S.image (· * γ₀), (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun γ _ => ?_
          by_cases hm : (γ : G) * x ∈ C <;> simp [hm]
      _ = ((S.image (· * γ₀)).card : ℝ≥0∞) := by simp
      _ ≤ S.card := by exact_mod_cast Finset.card_image_le
  · push_neg at h
    simp [h]

theorem lintegral_rep_le (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {C : Set G} (hC : MeasurableSet C)
    (S : Finset Γ) (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) {φ : G → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y in C, φ (r y) ∂μ ≤ S.card * ∫⁻ x in D, φ x ∂μ := by
  classical
  have hfix : ∀ᵐ x ∂μ.restrict D, ∀ γ : Γ, r ((γ : G) * x) = x := by
    filter_upwards [ae_restrict_of_ae (ae_good hD), ae_restrict_mem hDm] with x hx hxD γ
    rw [rep_mul hr hx γ]
    simpa using rep_eq hr hx (γ := 1) (by simpa using hxD)
  have hmeas : ∀ γ : Γ, AEMeasurable
      (fun x => C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x) (μ.restrict D) := fun γ =>
    (((measurable_const.indicator hC).comp (measurable_const_mul (γ : G))).mul hφ).aemeasurable
  calc ∫⁻ y in C, φ (r y) ∂μ = ∫⁻ y, C.indicator (fun y => φ (r y)) y ∂μ :=
        (lintegral_indicator hC _).symm
    _ = ∑' γ : Γ, ∫⁻ x in D, C.indicator (fun y => φ (r y)) (γ • x) ∂μ :=
        hD.lintegral_eq_tsum'' _
    _ = ∑' γ : Γ, ∫⁻ x in D, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x ∂μ := by
        refine tsum_congr fun γ => lintegral_congr_ae ?_
        filter_upwards [hfix] with x hx
        change C.indicator (fun y => φ (r y)) ((γ : G) * x) = _
        by_cases hm : (γ : G) * x ∈ C
        · simp [hm, hx γ]
        · simp [hm]
    _ = ∫⁻ x in D, ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x ∂μ :=
        (lintegral_tsum hmeas).symm
    _ = ∫⁻ x in D, (∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) * φ x ∂μ :=
        lintegral_congr fun x => ENNReal.tsum_mul_right
    _ ≤ ∫⁻ x in D, (S.card : ℝ≥0∞) * φ x ∂μ :=
        lintegral_mono fun x => by gcongr; exact card_le_of_translates_mem_mul_inv_tsum_indicator S hS x
    _ = S.card * ∫⁻ x in D, φ x ∂μ := lintegral_const_mul _ hφ

theorem integrableOn_rep (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {C : Set G} (hC : MeasurableSet C)
    (hCf : μ C ≠ ∞) (S : Finset Γ) (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) :
    ∃ M : ℝ, ∀ F : Lp ℂ 2 (μ.restrict D), IntegrableOn (fun y => F (r y)) C μ ∧
      ∫ y in C, ‖F (r y)‖ ∂μ ≤ M * ‖F‖ := by
  refine ⟨((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ)).toReal, fun F => ?_⟩
  haveI : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.2 hCf
  have hFm : Measurable (F : G → ℂ) := (Lp.stronglyMeasurable F).measurable
  have hgm : AEStronglyMeasurable (fun y => F (r y)) (μ.restrict C) :=
    (aestronglyMeasurable_comp_rep hD hDm hr (Lp.stronglyMeasurable F)).restrict
  have hcard : (S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.natCast_ne_top _)
  have hCr : μ C ^ (1 / 2 : ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCf
  have h2 : eLpNorm (fun y => F (r y)) 2 (μ.restrict C) ≤
      (S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm F 2 (μ.restrict D) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    gcongr
    exact lintegral_rep_le hD hDm hr hC S hS (φ := fun x => ‖F x‖ₑ ^ (2 : ℝ)) (by fun_prop)
  have h1 : eLpNorm (fun y => F (r y)) 1 (μ.restrict C) ≤
      eLpNorm (fun y => F (r y)) 2 (μ.restrict C) * μ C ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hgm
    rw [Measure.restrict_apply_univ] at h
    convert h using 3
    norm_num
  have hL2 : MemLp (fun y => F (r y)) 2 (μ.restrict C) :=
    ⟨hgm, h2.trans_lt (ENNReal.mul_lt_top hcard.lt_top (Lp.eLpNorm_lt_top F))⟩
  refine ⟨hL2.integrable (by norm_num), ?_⟩
  calc ∫ y in C, ‖F (r y)‖ ∂μ = (eLpNorm (fun y => F (r y)) 1 (μ.restrict C)).toReal := by
        rw [integral_norm_eq_lintegral_enorm hgm, eLpNorm_one_eq_lintegral_enorm]
    _ ≤ ((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm F 2 (μ.restrict D) * μ C ^ (1 / 2 : ℝ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hcard (Lp.eLpNorm_ne_top F)) hCr)
          (h1.trans (by gcongr))
    _ = ((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ)).toReal * ‖F‖ := by
        rw [Lp.norm_def, ← ENNReal.toReal_mul, mul_right_comm]

theorem ext_integrableOn : ∀ (B : RowsAut) (C : Set B.I.GA), IsCompact C → ∃ M : ℝ,
    ∀ F : B.I.L2 B.μf B.fund, IntegrableOn (B.I.ext F) C (B.I.muA B.μf) ∧
      ∫ y in C, ‖B.I.ext F y‖ ∂(B.I.muA B.μf) ≤ M * ‖F‖ := by
  intro B C hC
  obtain ⟨Γ, hΓ, hΓc, hfin, hfd⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain B.I
  obtain ⟨hT2, -, hsc, -⟩ := GlobalTheory.T.finiteAdelicUnitary_congruenceTopology B.I
  haveI := hΓc
  haveI := hT2
  haveI := hsc
  have hD := hfd B.μf B.fund B.fund_spec
  haveI : (B.I.muA B.μf).IsMulLeftInvariant := ⟨(GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf).1⟩
  haveI : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA
    infer_instance
  have hDm : MeasurableSet B.fund := B.fund_spec.1
  have hr : ∀ y, ∃ γ : Γ, B.I.rep B.fund y = (γ : B.I.GA) * y ∧ B.I.rep B.fund y ∈ B.fund := by
    intro y
    have h := B.fund_spec.2.1 y
    refine ⟨⟨h.choose, ?_⟩, ?_, ?_⟩
    · rw [← SetLike.mem_coe, hΓ]
      exact h.choose_spec.1
    · rw [AutInst.rep, dif_pos h]
    · rw [AutInst.rep, dif_pos h]
      exact h.choose_spec.2
  have hK : IsCompact (C * C⁻¹) := hC.mul hC.inv
  have hSfin : {γ : Γ | (γ : B.I.GA) ∈ C * C⁻¹}.Finite :=
    ((hfin _ hK).preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨hγ, by
      rw [← hΓ]
      exact γ.2⟩
  obtain ⟨M, hM⟩ := integrableOn_rep hD hDm hr hC.measurableSet hC.measure_lt_top.ne
    hSfin.toFinset fun γ hγ => hSfin.mem_toFinset.2 hγ
  exact ⟨M, fun F => hM F⟩

end GlobalTheory.LocalL2Isometry
