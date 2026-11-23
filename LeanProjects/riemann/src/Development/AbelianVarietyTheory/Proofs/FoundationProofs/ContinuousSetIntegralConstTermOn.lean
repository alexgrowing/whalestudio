import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemExtSubSpanDepth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstantTermAlongFlagEqZeroOfCuspidalStatement

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp
open scoped ENNReal Pointwise InnerProductSpace ComplexConjugate

namespace GlobalTheory.CuspAE

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ]
  {μ : Measure G} [μ.IsHaarMeasure] {φ : G → ℂ} {S : Set G}

omit [LocallyCompactSpace G] in

theorem exists_setIntegral_norm_le (hS : IsCompact S) :
    ∃ c : ℝ, ∀ F : L2 Γ μ, ∫ y in S, ‖lift Γ F y‖ ∂μ ≤ c * ‖F‖ := by
  set a : ℝ≥0∞ := ({γ : Γ | (γ : G) ∈ S * S⁻¹}.encard : ℝ≥0∞) with ha
  have ha' : a ≠ ∞ := by simpa [ha] using finite_mem_compact (Γ := Γ) (hS.mul hS.inv)
  have hle : (μ.restrict S).map (mk Γ) ≤ a • quotMeasure Γ μ := Measure.le_iff.2 fun A hA => by
    rw [Measure.map_apply measurable_mk hA, Measure.restrict_apply (measurable_mk hA),
      ← lintegral_indicator_one ((measurable_mk hA).inter hS.measurableSet),
      lintegral_eq_lintegral_tsum (Γ := Γ)
        (measurable_one.indicator ((measurable_mk hA).inter hS.measurableSet)).aemeasurable,
      Measure.smul_apply, smul_eq_mul, ← lintegral_indicator_one hA, ← lintegral_const_mul' _ _ ha']
    refine lintegral_mono fun q => le_trans (le_of_eq (tsum_congr fun γ => ?_))
      (AutomorphicL2Local.tsum_indicator_le Γ S q.out _)
    by_cases h1 : (γ : G) * q.out ∈ S <;> by_cases h2 : q ∈ A <;> simp [h1, h2]
  have hμ : μ S ≠ ∞ := hS.measure_lt_top.ne
  refine ⟨(a ^ (1 / 2 : ℝ) * μ S ^ (1 / 2 : ℝ)).toReal, fun F => ?_⟩
  have hm : AEStronglyMeasurable (lift Γ F) (μ.restrict S) :=
    ((Lp.stronglyMeasurable F).comp_measurable measurable_mk).aestronglyMeasurable
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm
  have h2 : eLpNorm (lift Γ F) 2 (μ.restrict S) ≤ a ^ (1 / 2 : ℝ) * eLpNorm F 2 (quotMeasure Γ μ) := by
    refine (eLpNorm_map_measure (Lp.stronglyMeasurable F).aestronglyMeasurable measurable_mk.aemeasurable).ge.trans
      ((eLpNorm_mono_measure _ hle).trans (le_of_eq ?_))
    rw [eLpNorm_smul_measure_of_ne_top (by norm_num)]
    norm_num
  rw [integral_norm_eq_lintegral_enorm hm, ← eLpNorm_one_eq_lintegral_enorm, Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (by have := Lp.eLpNorm_ne_top F; finiteness) (h1.trans ?_)
  rw [mul_right_comm, Measure.restrict_apply_univ]
  norm_num
  gcongr

omit [SecondCountableTopology G] [LocallyCompactSpace G] in

theorem setIntegral_norm_mul_left_le (hi : LocallyIntegrable φ μ) (hS : IsCompact S) {C : Set G} (hC : IsCompact C)
    {k : G} (hk : ∀ y ∈ S, k * y ∈ C) :
    IntegrableOn (fun y => φ (k * y)) S μ ∧ ∫ y in S, ‖φ (k * y)‖ ∂μ ≤ ∫ y in C, ‖φ y‖ ∂μ := by
  have hp := measurePreserving_mul_left μ k
  have he := measurableEmbedding_mulLeft k
  have h1 : IntegrableOn (fun y => φ (k * y)) ((k * ·) ⁻¹' C) μ :=
    (hp.integrableOn_comp_preimage he).2 (hi.integrableOn_isCompact hC)
  refine ⟨h1.mono_set hk, ?_⟩
  rw [← hp.setIntegral_preimage_emb he (fun y => ‖φ y‖) C]
  exact setIntegral_mono_set h1.norm (.of_forall fun _ => norm_nonneg _) (HasSubset.Subset.eventuallyLE hk)

omit [SecondCountableTopology G] [LocallyCompactSpace G] [DiscreteTopology Γ] in

theorem exists_compact_bound (hc : Cocompact Γ N) (hS : IsCompact S) : ∃ C : Set G, IsCompact C ∧
    ∀ φ : G → ℂ, LeftInv Γ φ → LocallyIntegrable φ μ → ∀ n : N,
      IntegrableOn (fun y => φ (n * y)) S μ ∧ ∫ y in S, ‖φ (n * y)‖ ∂μ ≤ ∫ y in C, ‖φ y‖ ∂μ := by
  obtain ⟨K, hK, hs⟩ := hc
  have hC := (hK.image continuous_subtype_val).mul hS
  refine ⟨_, hC, fun φ hφ hi n => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hs n
  simp only [← fun y => leftInv_integrand hφ y γ hγ n]
  exact setIntegral_norm_mul_left_le hi hS hC fun y hy => mul_mem_mul ⟨_, hk, rfl⟩ hy

variable [LocallyCompactSpace N]

theorem integrable_prod (hc : Cocompact Γ N) (hφ : LeftInv Γ φ) (hm : StronglyMeasurable φ)
    (hi : LocallyIntegrable φ μ) (hS : IsCompact S) :
    Integrable (fun p : Quot (Γ.subgroupOf N) × G => φ ((p.1.out : N) * p.2))
      ((probMeasure Γ N).prod (μ.restrict S)) := by
  have := hc.isProbabilityMeasure
  obtain ⟨C, -, hC⟩ := exists_compact_bound (μ := μ) hc hS
  have e : (fun p : Quot (Γ.subgroupOf N) × G => φ ((p.1.out : N) * p.2)) =
      fun p => φ ((sec (Γ.subgroupOf N) p.1 : N) * p.2) := funext fun p =>
    (leftInv_integrand hφ p.2).eq_of_mk_eq ((Quotient.out_eq _).trans (mk_sec _).symm)
  have hm' : StronglyMeasurable fun p : Quot (Γ.subgroupOf N) × G => φ ((p.1.out : N) * p.2) :=
    e ▸ hm.comp_measurable
      ((measurable_subtype_coe.comp (measurableEmbedding_sec.measurable.comp measurable_fst)).mul measurable_snd)
  refine (integrable_prod_iff hm'.aestronglyMeasurable).2 ⟨.of_forall fun q => (hC φ hφ hi q.out).1, ?_⟩
  refine .of_bound hm'.norm.integral_prod_right'.aestronglyMeasurable (∫ y in C, ‖φ y‖ ∂μ) (.of_forall fun q => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact (hC φ hφ hi q.out).2

theorem setIntegral_constTermOn (hc : Cocompact Γ N) (hφ : LeftInv Γ φ) (hm : StronglyMeasurable φ)
    (hi : LocallyIntegrable φ μ) (hS : IsCompact S) :
    ∫ y in S, constTermOn Γ N φ y ∂μ = ∫ q, ∫ y in S, φ ((q.out : N) * y) ∂μ ∂probMeasure Γ N := by
  have := hc.isProbabilityMeasure
  exact (integral_integral_swap (f := fun (q : Quot (Γ.subgroupOf N)) y => φ ((q.out : N) * y))
    (integrable_prod hc hφ hm hi hS)).symm

theorem locallyIntegrable_constTermOn (hc : Cocompact Γ N) (hφ : LeftInv Γ φ) (hm : StronglyMeasurable φ)
    (hi : LocallyIntegrable φ μ) : LocallyIntegrable (constTermOn Γ N φ) μ := by
  have := hc.isProbabilityMeasure
  exact locallyIntegrable_iff.2 fun S hS => (integrable_prod hc hφ hm hi hS).integral_prod_right

theorem constTermOn_convR (hc : Cocompact Γ N) (hφ : LeftInv Γ φ) (hm : StronglyMeasurable φ)
    (hi : LocallyIntegrable φ μ) {f : G → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) (x : G) :
    constTermOn Γ N (convR μ f φ) x = convR μ f (constTermOn Γ N φ) x := by
  have := hc.isProbabilityMeasure
  have hs' : HasCompactSupport fun y => f (x⁻¹ * y) := hs.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hs
  have h0 : ∀ u : G → ℂ, ∫ y in tsupport fun y => f (x⁻¹ * y), f (x⁻¹ * y) * u y ∂μ = ∫ y, f (x⁻¹ * y) * u y ∂μ :=
    fun u => setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [image_eq_zero_of_notMem_tsupport (f := fun y => f (x⁻¹ * y)) hy, zero_mul]
  have h1 := integral_integral_swap
    (f := fun (q : Quot (Γ.subgroupOf N)) y => f (x⁻¹ * y) * φ ((q.out : N) * y))
    ((integrable_prod hc hφ hm hi hs'.isCompact).bdd_mul (c := M)
      (Continuous.aestronglyMeasurable (f := fun y => f (x⁻¹ * y)) (by fun_prop)).comp_snd (.of_forall fun _ => hM _))
  simp only [h0, integral_const_mul] at h1
  rw [convR_eq]
  refine Eq.trans (integral_congr_ae (.of_forall fun q => ?_)) h1
  beta_reduce
  rw [← integral_mul_left_eq_self _ x]
  simp [convR, mul_assoc]

variable [μ.IsMulRightInvariant]

omit [LocallyCompactSpace N] in

theorem locallyIntegrable_lift (F : L2 Γ μ) : LocallyIntegrable (lift Γ F) μ :=
  locallyIntegrable_iff.2 fun C hC => (AutomorphicL2Local.memLp_restrict_compact G Γ μ F C hC).2

theorem continuous_setIntegral_constTermOn (hc : Cocompact Γ N) (hS : IsCompact S) :
    Continuous fun F : L2 Γ μ => ∫ y in S, constTermOn Γ N (lift Γ F) y ∂μ := by
  have := hc.isProbabilityMeasure
  obtain ⟨C, hC, h⟩ := exists_compact_bound (μ := μ) hc hS
  obtain ⟨c, hb⟩ := exists_setIntegral_norm_le (Γ := Γ) (μ := μ) hC
  have hm : ∀ F : L2 Γ μ, StronglyMeasurable (lift Γ F) := fun F =>
    (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  refine (LipschitzWith.of_dist_le' (K := c) fun F F' => ?_).continuous
  have hp := fun F : L2 Γ μ =>
    (integrable_prod hc (leftInv_lift F) (hm F) (locallyIntegrable_lift F) hS).integral_prod_left
  have h' := fun F : L2 Γ μ => h _ (leftInv_lift F) (locallyIntegrable_lift F)
  simp only [setIntegral_constTermOn hc (leftInv_lift _) (hm _) (locallyIntegrable_lift _) hS, dist_eq_norm]
  rw [← integral_sub (hp F) (hp F')]
  refine (norm_integral_le_of_norm_le_const (C := c * ‖F - F'‖) (.of_forall fun q => ?_)).trans (by simp)
  rw [← integral_sub (h' F q.out).1 (h' F' q.out).1]
  refine (norm_integral_le_integral_norm _).trans (le_trans (le_of_eq ?_) ((h' (F - F') q.out).2.trans (hb _)))
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [(measurePreserving_mul_left μ ((q.out : N) : G)).quasiMeasurePreserving.ae
    (ae_quotMeasure_iff.1 (Lp.coeFn_sub F F'))] with y hy
  exact congrArg norm hy.symm

theorem constTermOn_ae_eq_zero (hc : Cocompact Γ N) {F : L2 Γ μ} (hF : F ∈ closure {F : L2 Γ μ |
    ∃ φ, Continuous φ ∧ LeftInv Γ φ ∧ constTermOn Γ N φ = 0 ∧ lift Γ F =ᵐ[μ] φ}) :
    constTermOn Γ N (lift Γ F) =ᵐ[μ] 0 := by
  have hm : ∀ F : L2 Γ μ, StronglyMeasurable (lift Γ F) := fun F =>
    (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    (locallyIntegrable_constTermOn hc (leftInv_lift _) (hm F) (locallyIntegrable_lift F)) fun S hS => ?_
  refine closure_minimal ?_ (isClosed_eq (continuous_setIntegral_constTermOn hc hS) continuous_const) hF
  rintro F' ⟨φ, h1, h2, h3, h4⟩
  have h5 := setIntegral_constTermOn (μ := μ) hc h2 h1.stronglyMeasurable h1.locallyIntegrable hS
  rw [h3] at h5
  rw [mem_setOf_eq, setIntegral_constTermOn hc (leftInv_lift _) (hm _) (locallyIntegrable_lift _) hS]
  refine Eq.trans (integral_congr_ae (.of_forall fun q => integral_congr_ae (ae_restrict_of_ae ?_)))
    (h5.symm.trans (by simp))
  exact (measurePreserving_mul_left μ ((q.out : N) : G)).quasiMeasurePreserving.ae h4

omit [LocallyCompactSpace N] in

theorem mem_of_forall_Rop_mem {W : Submodule ℂ (L2 Γ μ)} (hW : IsClosed (W : Set (L2 Γ μ))) {F : L2 Γ μ}
    (h : ∀ f : G → ℂ, Continuous f → HasCompactSupport f → Rop Γ μ f F ∈ W) : F ∈ W := by
  have := hW.completeSpace_coe
  rw [← W.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro w hw
  have hu : Continuous fun g => ⟪w, R Γ μ g F⟫_ℂ := continuous_const.inner (continuous_R F)
  obtain ⟨b, hb1, -, hbc, hb⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : G)))
    isClosed_empty (disjoint_empty _)
  have hf : Continuous fun g => (b g : ℂ) * conj ⟪w, R Γ μ g F⟫_ℂ := by fun_prop
  have hs : HasCompactSupport fun g => (b g : ℂ) * conj ⟪w, R Γ μ g F⟫_ℂ :=
    (hbc.comp_left (g := Complex.ofReal) rfl).mul_right
  have hR := isRepOp_Rop (Γ := Γ) (hf.integrable_of_hasCompactSupport hs (μ := μ)) F
  have h1 := (W.mem_orthogonal' _).1 hw _ (h _ hf hs)
  rw [hR.2] at h1
  replace h1 := (integral_inner (𝕜 := ℂ) hR.1 w).trans h1
  have h2 : ∫ g, b g * ‖⟪w, R Γ μ g F⟫_ℂ‖ ^ 2 ∂μ = 0 := by
    rw [← Complex.ofReal_inj, ← integral_complex_ofReal, Complex.ofReal_zero, ← h1]
    refine integral_congr_ae (.of_forall fun g => ?_)
    beta_reduce
    rw [inner_smul_right, mul_assoc, Complex.conj_mul']
    simp
  by_contra h0
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (b.continuous.mul (hu.norm.pow 2)) hbc.mul_right
    (fun g => mul_nonneg (hb g).1 (sq_nonneg _)) ?_).ne' h2
  simpa [hb1 (mem_singleton _)] using h0

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_L2cusp_iff_isCuspAE : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (F : DividedPowerChartLift V μ), F ∈ L2cusp V μ ↔ IsCuspAE V μ F := by
  intro D V μ _ _ F
  refine ⟨fun h 𝔉 h𝔉 => constTermOn_ae_eq_zero (cocompact_flag D V 𝔉) (closure_mono ?_ h), fun h => ?_⟩
  · rintro F' ⟨φ, hφ, e⟩
    exact ⟨φ, hφ.1, hφ.2.1, T.constantTermAlongFlag_eq_zero_of_cuspidal D V φ hφ 𝔉 h𝔉, e⟩
  · refine mem_of_forall_Rop_mem (isSubrep_L2cusp V μ).1 fun f hf hs => ?_
    have hl := (leftInv_lift (Γ := GQ V) F).convR (μ := μ) f
    refine mem_L2cusp_of_ae_eq ⟨(AutomorphicL2Local.continuous_convR_lift _ _ μ f hf hs F).2, hl,
      isCuspFun_of_forall_flag hl fun 𝔉 h𝔉 => funext fun x => ?_⟩
      (AutomorphicL2Pointwise.lift_Rop_eq_convR _ _ μ f (hf.integrable_of_hasCompactSupport hs) F).2
    refine (constTermOn_convR (cocompact_flag D V 𝔉) (leftInv_lift _)
      ((Lp.stronglyMeasurable F).comp_measurable measurable_mk) (locallyIntegrable_lift F) hf hs x).trans ?_
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [(measurePreserving_mul_left μ x).quasiMeasurePreserving.ae (h 𝔉 h𝔉)] with y hy
    exact mul_eq_zero_of_right _ hy

end GlobalTheory.CuspAE
