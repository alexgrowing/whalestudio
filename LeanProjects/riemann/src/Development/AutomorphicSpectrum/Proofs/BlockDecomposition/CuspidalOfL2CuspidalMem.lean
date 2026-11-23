import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompact

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspL2

theorem exists_lintegral_enorm_lift_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {C : Set G} (hC : IsCompact C) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ F : L2 Γ μ, ∫⁻ g in C, ‖lift Γ F g‖ₑ ∂μ ≤ M * ‖F‖ₑ := by
  have hS : {γ : Γ | (γ : G) ∈ C * C⁻¹}.Finite := finite_mem_compact (hC.mul hC.inv)
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ≥0∞, N = ({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℝ≥0∞) := ⟨_, rfl⟩
  have hN : N ≠ ∞ := by simpa [hNdef] using hS
  have hfin : μ C ≠ ∞ := hC.measure_lt_top.ne
  refine ⟨N ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ), ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hN)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin), fun F => ?_⟩
  have hm : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have h2 : ∫⁻ g in C, ‖lift Γ F g‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ ≤
      N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ≥0∞).toReal ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
    rw [← lintegral_indicator hC.measurableSet,
      lintegral_eq_lintegral_tsum (Γ := Γ) ((hm.enorm.pow_const _).indicator hC.measurableSet),
      ← lintegral_const_mul' _ _ hN]
    refine lintegral_mono fun q => ?_
    rw [hNdef]
    refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (GlobalTheory.AutomorphicL2Local.tsum_indicator_le Γ C q.out _)
    by_cases hγ : (γ : G) * q.out ∈ C
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ]
      simp only [GlobalTheory.AutomorphicL2Unitary.lift, mk_mul, Quotient.out_eq]
    · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem hγ]
  have h3 : eLpNorm (lift Γ F) 2 (μ.restrict C) ≤ N ^ (1 / 2 : ℝ) * ‖F‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (f := F) (by simp) (by simp)]
    refine (ENNReal.rpow_le_rpow h2 (by simp)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp)]
    simp
  have h4 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict C) (p := 1) (q := 2) (by norm_num) hm.restrict
  have e : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [eLpNorm_one_eq_lintegral_enorm, e, Measure.restrict_apply_univ] at h4
  calc _ ≤ N ^ (1 / 2 : ℝ) * ‖F‖ₑ * μ C ^ (1 / 2 : ℝ) := h4.trans (by gcongr)
    _ = _ := by ring

section Adelic

variable {E : Type} [Field E] [NumberField E] {a r : ℕ}

theorem exists_mem_apply_unip_eq {X : Type*} {u : GA E a → X} (hl : ∀ γ g, u (ratGL E a γ * g) = u g)
    {K : Set (BlockIx a r → Ad E)} (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K) (x : BlockIx a r → Ad E) :
    ∃ k ∈ K, ∀ g, u (unip x * g) = u (unip k * g) := by
  obtain ⟨_, ⟨y, rfl⟩, hk⟩ := hcov x
  refine ⟨_, hk, fun g => ?_⟩
  rw [unip_add, mul_assoc]
  exact ((congrArg (fun v => u (v * _)) (unip_algebraMap y)).trans (hl _ _)).symm

variable [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]

theorem lintegral_constTerm_le [IsTotallyComplex E] (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (ν : Measure (BlockIx a r → Ad E)) {𝓕 : Set (BlockIx a r → Ad E)} (hν𝓕 : ν 𝓕 ≠ ∞)
    {K : Set (BlockIx a r → Ad E)} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K) {C : Set (GA E a)}
    (hC : IsCompact C) {u : GA E a → ℂ} (hc : Continuous u) (hl : ∀ γ g, u (ratGL E a γ * g) = u g) :
    ∫⁻ g in C, ‖∫ x in 𝓕, u (unip x * g) ∂ν‖ₑ ∂μ ≤ ν 𝓕 * ∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 hν𝓕
  haveI : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  have hC' : IsCompact ((unip '' K) * C) := (hK.image continuous_unip).mul hC
  have hb : ∀ x, ∫⁻ g in C, ‖u (unip x * g)‖ₑ ∂μ ≤ ∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ := fun x => by
    obtain ⟨k, hk, e⟩ := exists_mem_apply_unip_eq hl hcov x
    simp only [e]
    rw [← (measurePreserving_mul_left μ (unip k)).setLIntegral_comp_preimage hC'.measurableSet
      hc.enorm.measurable]
    exact lintegral_mono_set fun g hg => Set.mul_mem_mul ⟨k, hk, rfl⟩ hg
  have hj : Continuous fun p : GA E a × (BlockIx a r → Ad E) => ‖u (unip p.2 * p.1)‖ₑ :=
    (hc.comp ((continuous_unip.comp continuous_snd).mul continuous_fst)).enorm
  calc ∫⁻ g in C, ‖∫ x in 𝓕, u (unip x * g) ∂ν‖ₑ ∂μ
      ≤ ∫⁻ g in C, ∫⁻ x in 𝓕, ‖u (unip x * g)‖ₑ ∂ν ∂μ :=
        lintegral_mono fun g => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x in 𝓕, ∫⁻ g in C, ‖u (unip x * g)‖ₑ ∂μ ∂ν := lintegral_lintegral_swap hj.aemeasurable
    _ ≤ ∫⁻ x in 𝓕, (∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ) ∂ν := lintegral_mono hb
    _ = _ := by rw [setLIntegral_const, mul_comm]

theorem continuous_constTerm [IsTotallyComplex E] (ν : Measure (BlockIx a r → Ad E)) {𝓕 : Set (BlockIx a r → Ad E)}
    (hν𝓕 : ν 𝓕 ≠ ∞) {K : Set (BlockIx a r → Ad E)} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K)
    {u : GA E a → ℂ} (hc : Continuous u) (hl : ∀ γ g, u (ratGL E a γ * g) = u g) :
    Continuous fun g => ∫ x in 𝓕, u (unip x * g) ∂ν := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 hν𝓕
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g₀
  obtain ⟨B, hB⟩ := ((hK.image continuous_unip).mul hC).exists_bound_of_continuousOn hc.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => B)
    (.of_forall fun g => (hc.comp (continuous_unip.mul continuous_const)).aestronglyMeasurable) ?_
    (integrable_const _) (.of_forall fun x => (hc.comp (continuous_const.mul continuous_id)).continuousAt)
  filter_upwards [hg] with g hg'
  refine .of_forall fun x => ?_
  obtain ⟨k, hk, e⟩ := exists_mem_apply_unip_eq hl hcov x
  rw [e]
  exact hB _ (Set.mul_mem_mul ⟨k, hk, rfl⟩ hg')

end Adelic

theorem isCuspidal_of_toL2_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : GA E a → ℂ), Continuous φ →
    (∀ γ g, φ (ratGL E a γ * g) = φ g) → (∀ t g, φ (splitCentre E a t * g) = φ g) →
    ∀ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ L2cusp μ → IsCuspidal φ := by
  intro E _ _ _ a μ _ _ φ hc hl hs h hF r h0 h1 _ _ ν 𝓕 hν h𝓕 g
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.ConstNotCusp.discreteTopology_ratN E a r
  haveI : Countable (ratN E a r) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  have hν𝓕 : ν 𝓕 ≠ ∞ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK hcov ν h𝓕).ne
  have hcont := continuous_constTerm ν hν𝓕 hK hcov hc hl
  have key : ∀ C : Set (GA E a), IsCompact C → ∫⁻ g in C, ‖∫ x in 𝓕, φ (unip x * g) ∂ν‖ₑ ∂μ = 0 := fun C hC => by
    obtain ⟨M, hM, hb⟩ := exists_lintegral_enorm_lift_le (latticeGL E a) μ ((hK.image continuous_unip).mul hC)
    have step : ∀ F' ∈ cuspContinuousL2 μ, ∫⁻ g in C, ‖∫ x in 𝓕, φ (unip x * g) ∂ν‖ₑ ∂μ ≤ ν 𝓕 * (M * ‖h.toL2 - F'‖ₑ) := by
      rintro F' ⟨ψ, hψ, e⟩
      have hcomp : ∀ g, ∫ x in 𝓕, (φ (unip x * g) - ψ (unip x * g)) ∂ν = ∫ x in 𝓕, φ (unip x * g) ∂ν := fun g => by
        rw [integral_sub (integrableOn_unip hc hl ν h𝓕 g) (integrableOn_unip hψ.1 hψ.2.1 ν h𝓕 g),
          hψ.2.2.2 r h0 h1 ν 𝓕 hν h𝓕 g, sub_zero]
      have h2 := lintegral_constTerm_le μ ν hν𝓕 hK hcov hC (u := fun g => φ g - ψ g) (hc.sub hψ.1)
        (fun γ g => by rw [hl, hψ.2.1])
      simp only [hcomp] at h2
      have e' : lift (latticeGL E a) (h.toL2 - F') =ᵐ[μ] fun g => φ g - ψ g :=
        Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_sub h.toL2 F')) (h.lift_toL2_ae_eq.sub e)
      refine h2.trans ?_
      gcongr
      refine le_trans (le_of_eq (lintegral_congr_ae (ae_restrict_of_ae ?_))) (hb (h.toL2 - F'))
      exact e'.mono fun g eg => by rw [eg]
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (show h.toL2 ∈ closure (cuspContinuousL2 μ : Set _) from hF)
    have ht : Filter.Tendsto (fun n => ν 𝓕 * (M * ‖h.toL2 - u n‖ₑ)) Filter.atTop (𝓝 0) := by
      have h3 : Filter.Tendsto (fun n => h.toL2 - u n) Filter.atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := h.toL2)).sub hlim
      have h4 : Filter.Tendsto (fun n => ‖h.toL2 - u n‖ₑ) Filter.atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto _).comp h3
      simpa using ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul h4 (Or.inr hM)) (Or.inr hν𝓕)
    exact le_antisymm (ge_of_tendsto' ht fun n => step _ (hu n)) zero_le
  have hae : (fun g => ∫ x in 𝓕, φ (unip x * g) ∂ν) =ᵐ[μ] 0 := by
    have h5 : ∀ n, ∀ᵐ g ∂μ.restrict (compactCovering (GA E a) n), ∫ x in 𝓕, φ (unip x * g) ∂ν = 0 := fun n => by
      have := (lintegral_eq_zero_iff' hcont.enorm.aemeasurable).1 (key _ (isCompact_compactCovering _ n))
      exact this.mono fun g eg => by simpa using eg
    have h6 := ae_restrict_iUnion_iff _ _ |>.2 h5
    rwa [iUnion_compactCovering, Measure.restrict_univ] at h6
  exact congrFun ((Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hae) g

end GlobalTheory.CompanionTheory.CuspL2

end
