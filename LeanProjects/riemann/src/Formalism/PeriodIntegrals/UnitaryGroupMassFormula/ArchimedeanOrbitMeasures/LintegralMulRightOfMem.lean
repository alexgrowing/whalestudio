import Mathlib

noncomputable section

namespace PI.AprimeInfA

open MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal NNReal

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  let _ := TopologicalSpace.metrizableSpaceMetric Y
  have hemb : IsEmbedding ((↑) : Y → UniformSpace.Completion Y) :=
    (UniformSpace.Completion.isUniformEmbedding_coe Y).isEmbedding
  have hdense : DenseRange ((↑) : Y → UniformSpace.Completion Y) :=
    UniformSpace.Completion.denseRange_coe
  have hopen : IsOpen (range ((↑) : Y → UniformSpace.Completion Y)) := by
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨y, rfl⟩
    obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
    obtain ⟨V, hVK, hVo, hyV⟩ := mem_nhds_iff.1 hKy
    obtain ⟨U, hUo, hUV⟩ := hemb.isInducing.isOpen_iff.1 hVo
    refine ⟨U, ?_, hUo, ?_⟩
    · have hcl : IsClosed (((↑) : Y → UniformSpace.Completion Y) '' K) :=
        (hK.image hemb.continuous).isClosed
      calc U ⊆ closure (U ∩ range ((↑) : Y → UniformSpace.Completion Y)) :=
            hdense.open_subset_closure_inter hUo
        _ ⊆ closure (((↑) : Y → UniformSpace.Completion Y) '' K) := by
            apply closure_mono
            rintro _ ⟨hz, ⟨z, rfl⟩⟩
            refine ⟨z, hVK ?_, rfl⟩
            rw [← hUV]
            exact hz
        _ = ((↑) : Y → UniformSpace.Completion Y) '' K := hcl.closure_eq
        _ ⊆ range ((↑) : Y → UniformSpace.Completion Y) := image_subset_range _ _
    · show y ∈ ((↑) : Y → UniformSpace.Completion Y) ⁻¹' U
      rw [hUV]
      exact hyV
  have : PolishSpace (range ((↑) : Y → UniformSpace.Completion Y)) := hopen.polishSpace
  exact hemb.toHomeomorph.isClosedEmbedding.polishSpace

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem map_mul_right_eq (μ : Measure G) [μ.IsHaarMeasure] (g : G) :
    μ.map (· * g) = Measure.modularCharacterFun g • μ := by

  rw [MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor μ g]
  exact Measure.isMulLeftInvariant_eq_smul _ μ

theorem measurable_modChar :
    Measurable (fun g : G => (Measure.modularCharacterFun g : ℝ≥0∞)) := by

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  set μ : Measure G := Measure.haar
  have hpos : μ K ≠ 0 := by
    first
    | exact (Measure.measure_pos_of_mem_nhds μ hK1).ne'
    | exact (MeasureTheory.measure_pos_of_mem_nhds μ hK1).ne'
    | exact ((isOpen_interior.measure_pos μ ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).trans_le
        (measure_mono interior_subset)).ne'
  have hfin : μ K ≠ ∞ := hK.measure_lt_top.ne
  have key : (fun g : G => (Measure.modularCharacterFun g : ℝ≥0∞)) =
      fun g => (∫⁻ x, K.indicator 1 (x * g) ∂μ) / μ K := by
    funext g
    have e := congrArg (fun m : Measure G => m K) (map_mul_right_eq μ g)
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    rw [Measure.map_apply (measurable_mul_const g) hK.measurableSet] at e
    rw [ENNReal.eq_div_iff hpos hfin, mul_comm, ← e,
      ← lintegral_indicator_one (hK.measurableSet.preimage (measurable_mul_const g))]
    rfl
  rw [key]
  refine Measurable.div_const ?_ _
  exact ((measurable_one.indicator hK.measurableSet).comp
    (measurable_snd.mul measurable_fst)).lintegral_prod_right'

theorem modChar_eq_one (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (k : H) : Measure.modularCharacterFun (k : G) = 1 := by

  haveI : MeasurableMul H := by
    first
    | infer_instance
    | exact ⟨fun c => ((measurable_const_mul (c : G)).comp measurable_subtype_coe).subtype_mk,
        fun c => ((measurable_mul_const (c : G)).comp measurable_subtype_coe).subtype_mk⟩
  obtain ⟨D, hD⟩ : ∃ D : H → ℝ, ∀ h, D h = (Measure.modularCharacterFun (h : G) : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have hDm : Measurable D := by
    rw [show D = fun h : H => (Measure.modularCharacterFun (h : G) : ℝ) from funext hD]
    exact measurable_coe_nnreal_real.comp
      ((measurable_coe_nnreal_ennreal_iff.1 measurable_modChar).comp measurable_subtype_coe)
  have hmul : ∀ a b : H, D (a * b) = D a * D b := by
    intro a b
    have e : Measure.modularCharacterFun ((a : G) * b) =
        Measure.modularCharacterFun (a : G) * Measure.modularCharacterFun (b : G) :=
      map_mul (Measure.modularCharacter (G := G)) (a : G) (b : G)
    rw [hD, hD, hD, Subgroup.coe_mul, e, NNReal.coe_mul]
  have hone : D 1 = 1 := by
    have e : Measure.modularCharacterFun (1 : G) = 1 := map_one (Measure.modularCharacter (G := G))
    rw [hD, OneMemClass.coe_one, e, NNReal.coe_one]
  have hpos : ∀ a : H, 0 < D a := by
    intro a
    have e : D a * D a⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    have hne0 : D a ≠ 0 := left_ne_zero_of_mul_eq_one e
    rw [hD] at hne0 ⊢
    exact lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hne0)
  by_contra hne
  have hc : D k ≠ 1 := by
    intro e
    rw [hD] at e
    exact hne (by exact_mod_cast e)
  obtain ⟨t, ht_def⟩ : ∃ t, t = Real.log (D k) := ⟨_, rfl⟩
  have ht : t ≠ 0 := by
    intro e
    rw [ht_def] at e
    rcases Real.log_eq_zero.1 e with h | h | h
    · exact (hpos k).ne' h
    · exact hc h
    · linarith [hpos k]
  have hinv : D k⁻¹ = (D k)⁻¹ := by
    have e := hmul k⁻¹ k
    rw [inv_mul_cancel, hone] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have hN : ∀ h : H, ⌊Real.log (D (k⁻¹ * h)) / t⌋ = ⌊Real.log (D h) / t⌋ - 1 := by
    intro h
    have e2 : Real.log (D (k⁻¹ * h)) / t = Real.log (D h) / t - 1 := by
      rw [hmul, hinv, Real.log_mul (inv_ne_zero (hpos k).ne') (hpos h).ne', Real.log_inv, ← ht_def,
        add_div, neg_div, div_self ht]
      ring
    rw [e2, Int.floor_sub_one]
  have hA : ∀ m : ℤ, ν {h : H | ⌊Real.log (D h) / t⌋ = m + 1} =
      ν {h : H | ⌊Real.log (D h) / t⌋ = m} := by
    intro m
    have e : {h : H | ⌊Real.log (D h) / t⌋ = m + 1} =
        (fun h => k⁻¹ * h) ⁻¹' {h : H | ⌊Real.log (D h) / t⌋ = m} := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hN]
      constructor <;> intro hh <;> omega
    rw [e, measure_preimage_mul]
  have hall : ∀ m : ℤ, ν {h : H | ⌊Real.log (D h) / t⌋ = m} =
      ν {h : H | ⌊Real.log (D h) / t⌋ = 0} := by
    intro m
    induction m using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hA, ih]
    | pred n ih => rw [← ih, ← hA, sub_add_cancel]
  have hU : (⋃ m : ℤ, {h : H | ⌊Real.log (D h) / t⌋ = m}) = Set.univ := by
    ext h
    simp
  have hdisj : Pairwise (Function.onFun Disjoint fun m : ℤ => {h : H | ⌊Real.log (D h) / t⌋ = m}) := by
    intro i j hij
    exact Set.disjoint_left.2 (fun h hi hj => hij (hi.symm.trans hj))
  have hmeas : ∀ m : ℤ, MeasurableSet {h : H | ⌊Real.log (D h) / t⌋ = m} := fun m =>
    (Int.measurable_floor.comp ((Real.measurable_log.comp hDm).div_const t))
      (measurableSet_singleton m)
  have htot : ν univ = ∑' _m : ℤ, ν {h : H | ⌊Real.log (D h) / t⌋ = 0} := by
    rw [← hU, measure_iUnion hdisj hmeas]
    exact tsum_congr hall
  by_cases hz : ν {h : H | ⌊Real.log (D h) / t⌋ = 0} = 0
  · rw [hz, tsum_zero] at htot
    exact h0 htot
  · rw [ENNReal.tsum_const_eq_top_of_ne_zero hz] at htot
    exact hfin htot

theorem lintegral_mul_right_of_mem (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
    (ν : Measure H) [ν.IsMulLeftInvariant] (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (k : H)
    {f : G → ℝ≥0∞} (hf : Measurable f) : ∫⁻ g, f (g * k) ∂μ = ∫⁻ g, f g ∂μ := by

  rw [show (∫⁻ g, f (g * k) ∂μ) = ∫⁻ g, f g ∂(μ.map (· * (k : G))) from
    (lintegral_map hf (measurable_mul_const _)).symm, map_mul_right_eq μ (k : G),
    modChar_eq_one H ν h0 hfin k, one_smul]

theorem meas_avg (H : Subgroup G) (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun g : G => ∫⁻ h, f (g * (h : G)) ∂ν) := by

  exact (hf.comp (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))).lintegral_prod_right'

theorem avg_mul_mem (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞)
    (g : G) (k : H) : ∫⁻ h, f (g * k * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by

  haveI : MeasurableMul H := by
    first
    | infer_instance
    | exact ⟨fun c => ((measurable_const_mul (c : G)).comp measurable_subtype_coe).subtype_mk,
        fun c => ((measurable_mul_const (c : G)).comp measurable_subtype_coe).subtype_mk⟩
  have e := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (g * (h : G))) k
  simpa [mul_assoc] using e

theorem avg_out (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by

  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hk]
  exact avg_mul_mem H ν f g k

theorem meas_avg_q (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) := by

  refine measurable_from_quotient.2 ?_
  convert meas_avg H ν hf using 1
  funext g
  exact avg_out H ν f g

variable {X : Type} [MulAction G X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

theorem orb_mk (x0 : X) (g : G) :
    ((g : G ⧸ MulAction.stabilizer G x0)).out • x0 = g • x0 := by

  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (MulAction.stabilizer G x0) g
  rw [hk, mul_smul, MulAction.mem_stabilizer_iff.mp k.2]

theorem orb_cont (x0 : X) (hc : Continuous fun g : G => g • x0) :
    Continuous (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by

  have e : (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) ∘ QuotientGroup.mk =
      fun g : G => g • x0 := by
    funext g
    exact orb_mk x0 g
  exact (QuotientGroup.isQuotientMap_mk (MulAction.stabilizer G x0)).continuous_iff.2 (by rw [e]; exact hc)

theorem orb_inj (x0 : X) :
    Function.Injective (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by

  intro q q' h
  simp only at h
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
    MulAction.mem_stabilizer_iff, mul_smul, ← h, ← mul_smul, inv_mul_cancel, one_smul]

theorem unfold_stab (x0 : X) (hc : Continuous fun g : G => g • x0) (μ : Measure G)
    [μ.IsHaarMeasure] (ν : Measure (MulAction.stabilizer G x0)) (hν : ν.IsMulLeftInvariant)
    (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (f : G → ℝ≥0∞) (hf : Measurable f) (s : X → G)
    (hs : ∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) :
    ∫⁻ g, f g ∂μ = (ν univ)⁻¹ *
      ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂ν ∂(μ.map (fun g => g • x0)) := by
  haveI := hν
  haveI : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.2 hfin⟩
  have hS : IsClosed ((MulAction.stabilizer G x0 : Subgroup G) : Set G) := by
    have e : ((MulAction.stabilizer G x0 : Subgroup G) : Set G) = (fun g : G => g • x0) ⁻¹' {x0} := by
      ext g
      exact MulAction.mem_stabilizer_iff
    rw [e]
    exact isClosed_singleton.preimage hc
  haveI : IsClosed ((MulAction.stabilizer G x0 : Subgroup G) : Set G) := hS
  haveI : PolishSpace (G ⧸ MulAction.stabilizer G x0) := polish_of_lcsc _
  haveI : PolishSpace G := polish_of_lcsc G
  have hqc : Continuous (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0) :=
    (QuotientGroup.isQuotientMap_mk _).continuous
  haveI : BorelSpace (G ⧸ MulAction.stabilizer G x0) := by
    refine ⟨le_antisymm ?_ ?_⟩
    · intro A hA
      have hA' : MeasurableSet ((QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0) ⁻¹' A) := hA
      have hAc' : MeasurableSet ((QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0) ⁻¹' Aᶜ) :=
        hA'.compl
      letI : MeasurableSpace (G ⧸ MulAction.stabilizer G x0) := borel _
      haveI : BorelSpace (G ⧸ MulAction.stabilizer G x0) := ⟨rfl⟩
      have h1 : AnalyticSet A := by
        rw [← Set.image_preimage_eq A QuotientGroup.mk_surjective]
        exact hA'.analyticSet_image hqc.measurable
      have h2 : AnalyticSet Aᶜ := by
        rw [← Set.image_preimage_eq Aᶜ QuotientGroup.mk_surjective]
        exact hAc'.analyticSet_image hqc.measurable
      exact h1.measurableSet_of_compl h2
    · refine MeasurableSpace.generateFrom_le ?_
      intro U hU
      exact (hU.preimage hqc).measurableSet
  have hπ : MeasurableEmbedding (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) :=
    (orb_cont x0 hc).measurableEmbedding (orb_inj x0)
  have hmk : Measurable (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0) := by
    first
    | exact measurable_quotient_mk''
    | exact measurable_quotient_mk'
    | exact (QuotientGroup.continuous_mk).measurable
    | exact continuous_quot_mk.measurable
    | fun_prop
  have hmap : μ.map (fun g => g • x0) =
      (μ.map (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0)).map
        (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by
    rw [Measure.map_map hπ.measurable hmk]
    congr 1
    funext g
    exact (orb_mk x0 g).symm
  have hFs : ∀ q : G ⧸ MulAction.stabilizer G x0,
      ∫⁻ h', f (s (q.out • x0) * (h' : G)) ∂ν = ∫⁻ h', f (q.out * (h' : G)) ∂ν := by
    intro q
    have hy : s (q.out • x0) • x0 = q.out • x0 := hs _ ⟨q.out, rfl⟩
    have hk : (q.out)⁻¹ * s (q.out • x0) ∈ MulAction.stabilizer G x0 := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hy, ← mul_smul, inv_mul_cancel, one_smul]
    have e : s (q.out • x0) = q.out * ((q.out)⁻¹ * s (q.out • x0)) := by group
    rw [e]
    exact avg_mul_mem (MulAction.stabilizer G x0) ν f q.out ⟨_, hk⟩
  have hinner : ∀ k : MulAction.stabilizer G x0, ∫⁻ g, f (g * k) ∂μ = ∫⁻ g, f g ∂μ := fun k =>
    lintegral_mul_right_of_mem μ (MulAction.stabilizer G x0) ν h0 hfin k hf
  rw [hmap, hπ.lintegral_map]
  simp only [hFs]
  rw [lintegral_map (meas_avg_q (MulAction.stabilizer G x0) ν hf) hmk]
  simp only [avg_out]
  rw [lintegral_lintegral_swap (f := fun (g : G) (h : MulAction.stabilizer G x0) => f (g * (h : G)))
    ((hf.comp (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))).aemeasurable)]
  simp only [hinner, lintegral_const]
  rw [mul_comm (∫⁻ g, f g ∂μ), ← mul_assoc, ENNReal.inv_mul_cancel h0 hfin, one_mul]

end Abstract

end PI.AprimeInfA
