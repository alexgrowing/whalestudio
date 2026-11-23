import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStrictMeasurableFundamentalSetOfDiscrete

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GenUnfold

theorem covol_eq_of_strict {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) (hμ : ∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) {F : Set G}
    (hF : MeasurableSet F) (h : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) :
    covol (Γ : Set G) μ Set.univ = μ F := by
  classical
  have hmeas : ∀ a : G, Measurable (fun y : G => a * y) := fun a => measurable_const_mul a
  unfold covol
  apply le_antisymm
  · refine iInf_le_of_le F (iInf_le_of_le hF (iInf_le_of_le ?_ le_rfl))
    intro x _
    obtain ⟨γ, hγ, -⟩ := h x
    exact ⟨γ, γ.2, hγ⟩
  · refine le_iInf fun D => le_iInf fun hD => le_iInf fun hcov => ?_

    have hsub : F ⊆ ⋃ γ : Γ, F ∩ (fun y => (γ : G) * y) ⁻¹' D := by
      intro x hx
      obtain ⟨γ, hγ, hxD⟩ := hcov x trivial
      exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, hx, hxD⟩

    have hpiece : ∀ γ : Γ, μ (F ∩ (fun y => (γ : G) * y) ⁻¹' D) =
        μ ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := by
      intro γ
      have hS : MeasurableSet ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := (hmeas _ hF).inter hD
      have e : (μ.map (fun y => (γ : G) * y)) ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) =
          μ ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := by rw [hμ γ γ.2]
      rw [Measure.map_apply (hmeas _) hS] at e
      rw [← e]
      congr 1
      ext y
      simp [inv_mul_cancel_left]

    have hdisj : Pairwise (Function.onFun Disjoint
        fun γ : Γ => (fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := by
      intro γ₁ γ₂ hne
      refine Set.disjoint_left.2 fun y hy₁ hy₂ => hne ?_
      obtain ⟨δ, -, huniq⟩ := h y
      have e₁ := huniq γ₁⁻¹ (by simpa using hy₁.1)
      have e₂ := huniq γ₂⁻¹ (by simpa using hy₂.1)
      exact inv_injective (e₁.trans e₂.symm)
    calc μ F ≤ μ (⋃ γ : Γ, F ∩ (fun y => (γ : G) * y) ⁻¹' D) := measure_mono hsub
      _ ≤ ∑' γ : Γ, μ (F ∩ (fun y => (γ : G) * y) ⁻¹' D) := measure_iUnion_le _
      _ = ∑' γ : Γ, μ ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := tsum_congr hpiece
      _ = μ (⋃ γ : Γ, (fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) :=
          (measure_iUnion hdisj fun γ => (hmeas _ hF).inter hD).symm
      _ ≤ μ D := measure_mono (Set.iUnion_subset fun _ => Set.inter_subset_right)

theorem isInvInvariant {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hUo : IsOpen (interior K) := isOpen_interior
  have hUpos : μ (interior K) ≠ 0 :=
    (hUo.measure_pos μ ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have hUfin : μ (interior K) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono interior_subset) hK.measure_lt_top).ne
  have hc := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  set c := Measure.haarScalarFactor μ.inv μ
  have key : ∀ s : Set G, MeasurableSet s → μ (Inv.inv ⁻¹' s) = (c : ENNReal) * μ s := by
    intro s hs
    have e : μ.inv s = (c • μ) s := by rw [← hc]
    rw [Measure.inv_def, Measure.map_apply measurable_inv hs, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul] at e
    exact e
  have h1 := key (interior K) hUo.measurableSet
  have h2 := key (Inv.inv ⁻¹' interior K) (hUo.measurableSet.preimage measurable_inv)
  have hUU : (Inv.inv ⁻¹' (Inv.inv ⁻¹' interior K) : Set G) = interior K := by
    ext x
    simp
  rw [hUU, h1, ← mul_assoc] at h2
  have hcc : (c : ENNReal) * c = 1 :=
    (ENNReal.mul_left_inj hUpos hUfin).1 (h2.symm.trans (one_mul _).symm)
  have hc1 : c = 1 := by
    have hnn : c * c = 1 := by exact_mod_cast hcc
    have hr : (c : ℝ) * c = 1 := by exact_mod_cast hnn
    have h0 : (0 : ℝ) ≤ c := c.2
    exact NNReal.eq (by push_cast; nlinarith)
  constructor
  rw [hc, hc1, one_smul]

private lemma exists_nhds_one_inter_discrete_subgroup_eq_one {H : Type} [Group H] [TopologicalSpace H] (Γ : Subgroup H)
    [DiscreteTopology Γ] : ∃ V ∈ nhds (1 : H), ∀ γ ∈ Γ, γ ∈ V → γ = 1 := by

  have ho : IsOpen ({1} : Set Γ) := isOpen_discrete _
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.1 ho
  have h1 : (1 : Γ) ∈ (Subtype.val ⁻¹' t : Set Γ) := by
    rw [hpre]
    exact Set.mem_singleton _
  refine ⟨t, ht.mem_nhds h1, fun γ hγ hγt => ?_⟩
  have h2 : (⟨γ, hγ⟩ : Γ) ∈ (Subtype.val ⁻¹' t : Set Γ) := hγt
  rw [hpre] at h2
  have h3 : (⟨γ, hγ⟩ : Γ) = 1 := h2
  simpa using congrArg Subtype.val h3

theorem exists_nhds_map {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsEmbedding j) (Γ : Subgroup H) [DiscreteTopology Γ] :
    ∃ U ∈ nhds (1 : G), ∀ γ ∈ Γ.map j, γ ∈ U → γ = 1 := by
  obtain ⟨V, hV, hVΓ⟩ := exists_nhds_one_inter_discrete_subgroup_eq_one Γ
  rw [hj.isInducing.nhds_eq_comap (1 : H), map_one] at hV
  obtain ⟨U, hU, hUV⟩ := Filter.mem_comap.1 hV
  refine ⟨U, hU, fun γ hγ hγU => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hγ
  rw [hVΓ x hx (hUV hγU), map_one]

theorem covol_withDensity_eq : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (Γ : Subgroup H) [DiscreteTopology Γ] (Φ b : G → ENNReal), Measurable Φ → Measurable b → (∀ h g, Φ (j h * g) = Φ g) → (∀ g, ∫⁻ h, b (j h * g) ∂ν = 1) → covol ((Γ.map j : Subgroup G) : Set G) (μ.withDensity Φ) Set.univ = covol (Γ : Set H) ν Set.univ * ∫⁻ g, Φ g * b g ∂μ := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ j hj Γ _ Φ b hΦ hb hΦinv hb1
  classical
  have hjc : Continuous j := hj.continuous
  have : ν.IsInvInvariant := isInvInvariant ν

  obtain ⟨hcnt, F, hFm, hF⟩ := GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete G
    (Γ.map j) (exists_nhds_map j hj.toIsEmbedding Γ)
  have := hcnt
  have hcntH : Countable Γ :=
    Function.Injective.countable
      (f := fun γ : Γ => (⟨j γ, Subgroup.mem_map_of_mem j γ.2⟩ : Γ.map j))
      (fun a b hab => Subtype.ext (hj.injective (congrArg Subtype.val hab)))

  have hL : covol ((Γ.map j : Subgroup G) : Set G) (μ.withDensity Φ) Set.univ =
      ∫⁻ g in F, Φ g ∂μ := by
    rw [covol_eq_of_strict (Γ.map j) (μ.withDensity Φ) ?_ hFm hF, withDensity_apply _ hFm]
    intro γ hγ
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hγ
    ext s hs
    rw [Measure.map_apply (measurable_const_mul _) hs,
      withDensity_apply _ (measurable_const_mul _ hs), withDensity_apply _ hs,
      ← lintegral_indicator (measurable_const_mul _ hs), ← lintegral_indicator hs,
      ← lintegral_mul_left_eq_self (s.indicator Φ) (j x)]
    refine lintegral_congr fun y => ?_
    simp only [Set.indicator_apply, Set.mem_preimage, hΦinv]

  have hfib : ∀ g : G, ν {x : H | (j x)⁻¹ * g ∈ F} = covol (Γ : Set H) ν Set.univ := by
    intro g
    have hT : MeasurableSet {x : H | j x * g ∈ F} :=
      hFm.preimage (hjc.mul continuous_const).measurable
    have e₁ : {x : H | (j x)⁻¹ * g ∈ F} = Inv.inv ⁻¹' {x : H | j x * g ∈ F} := by
      ext x
      simp [map_inv]
    rw [e₁, Measure.measure_preimage_inv,
      covol_eq_of_strict Γ ν (fun γ _ => map_mul_left_eq_self ν γ) hT]
    intro x
    obtain ⟨δ, hδ, huniq⟩ := hF (j x * g)
    obtain ⟨γ, hγ, hδe⟩ := Subgroup.mem_map.1 δ.2
    refine ⟨⟨γ, hγ⟩, ?_, ?_⟩
    · show j (γ * x) * g ∈ F
      rw [map_mul, mul_assoc, hδe]
      exact hδ
    · rintro ⟨γ', hγ'⟩ h'
      have h'' : ((⟨j γ', Subgroup.mem_map_of_mem j hγ'⟩ : Γ.map j) : G) * (j x * g) ∈ F := by
        have h3 : j (γ' * x) * g ∈ F := h'
        simpa [map_mul, mul_assoc] using h3
      have e₂ := huniq _ h''
      apply Subtype.ext
      apply hj.injective
      show j γ' = j γ
      rw [hδe]
      exact congrArg Subtype.val e₂
  have hm₁ : Measurable (fun p : G × H => j p.2 * p.1) :=
    ((hjc.comp continuous_snd).mul continuous_fst).measurable
  have hm₂ : Measurable (fun p : H × G => (j p.1)⁻¹ * p.2) :=
    ((hjc.comp continuous_fst).inv.mul continuous_snd).measurable
  have hm₃ : ∀ g : G, Measurable (fun x : H => (j x)⁻¹ * g) :=
    fun g => (hjc.inv.mul continuous_const).measurable
  have hbm : ∀ g : G, Measurable (fun x : H => b (j x * g)) :=
    fun g => hb.comp (hjc.mul continuous_const).measurable
  have hI : Measurable (F.indicator (1 : G → ENNReal)) := measurable_one.indicator hFm
  rw [hL]
  calc ∫⁻ g in F, Φ g ∂μ
      = ∫⁻ g, F.indicator 1 g * Φ g * ∫⁻ x, b (j x * g) ∂ν ∂μ := by
        rw [← lintegral_indicator hFm]
        refine lintegral_congr fun g => ?_
        rw [hb1 g, mul_one]
        by_cases hg : g ∈ F <;> simp [hg]
    _ = ∫⁻ g, ∫⁻ x, F.indicator 1 g * Φ g * b (j x * g) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul _ (hbm g)]
    _ = ∫⁻ x, ∫⁻ g, F.indicator 1 g * Φ g * b (j x * g) ∂μ ∂ν := by
        apply lintegral_lintegral_swap
        exact (((hI.comp measurable_fst).mul (hΦ.comp measurable_fst)).mul
          (hb.comp hm₁)).aemeasurable
    _ = ∫⁻ x, ∫⁻ g, F.indicator 1 ((j x)⁻¹ * g) * Φ g * b g ∂μ ∂ν := by
        refine lintegral_congr fun x => ?_
        have e := lintegral_mul_left_eq_self (μ := μ)
          (fun g => F.indicator 1 ((j x)⁻¹ * g) * Φ g * b g) (j x)
        simpa only [inv_mul_cancel_left, hΦinv] using e
    _ = ∫⁻ g, ∫⁻ x, F.indicator 1 ((j x)⁻¹ * g) * Φ g * b g ∂ν ∂μ := by
        apply lintegral_lintegral_swap
        exact (((hI.comp hm₂).mul (hΦ.comp measurable_snd)).mul
          (hb.comp measurable_snd)).aemeasurable
    _ = ∫⁻ g, ν {x : H | (j x)⁻¹ * g ∈ F} * (Φ g * b g) ∂μ := by
        refine lintegral_congr fun g => ?_
        have hmg : MeasurableSet {x : H | (j x)⁻¹ * g ∈ F} := hFm.preimage (hm₃ g)
        simp_rw [mul_assoc]
        rw [lintegral_mul_const (f := fun x => F.indicator 1 ((j x)⁻¹ * g)) _ (hI.comp (hm₃ g)),
          ← lintegral_indicator_one hmg]
        rfl
    _ = ∫⁻ g, covol (Γ : Set H) ν Set.univ * (Φ g * b g) ∂μ := by
        simp_rw [hfib]
    _ = covol (Γ : Set H) ν Set.univ * ∫⁻ g, Φ g * b g ∂μ :=
        lintegral_const_mul _ (hΦ.mul hb)

end GlobalTheory.GenUnfold
