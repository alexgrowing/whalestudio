import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot

open MeasureTheory Topology Filter Set
open scoped ENNReal Pointwise

noncomputable section

namespace CompanionTheory.D.gk.RF

theorem Disc.countable {G : Type} [Group G] [TopologicalSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {Λ : Subgroup G} (h : Disc Λ) : Countable Λ := by
  have : (Λ : Set G).Countable := by
    have e : (Λ : Set G) = ⋃ n, compactCovering G n ∩ Λ := by rw [← iUnion_inter, iUnion_compactCovering, univ_inter]
    rw [e]
    exact countable_iUnion fun n => (h _ (isCompact_compactCovering G n)).countable
  exact this.to_subtype

theorem Disc.exists_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] {Λ : Subgroup G} (h : Disc Λ) :
    ∃ O ∈ 𝓝 (1 : G), ∀ a ∈ O, ∀ b ∈ O, a * b⁻¹ ∈ Λ → a = b := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hcl : IsClosed ((K ∩ Λ) \ {1}) := ((h K hK).subset sdiff_subset).isClosed
  have hW : K ∩ ((K ∩ Λ) \ {1})ᶜ ∈ 𝓝 (1 : G) := inter_mem hK1 (hcl.isOpen_compl.mem_nhds fun h => h.2 rfl)
  obtain ⟨O, hO, hOW⟩ := exists_nhds_split_inv hW
  refine ⟨O, hO, fun a ha b hb hab => ?_⟩
  have := hOW a ha b hb
  rw [div_eq_mul_inv] at this
  by_contra hne
  exact this.2 ⟨⟨this.1, hab⟩, fun e => hne (mul_inv_eq_one.1 e)⟩

theorem fundamental_domain_inclusion : FundIn := by
  classical
  intro N _ _ _ _ _ _ _ _ Λ hd V hV hcov
  obtain ⟨O, hO, hinj⟩ := hd.exists_nhds
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.countable_cover_nhds
    (f := fun p : N => interior ((fun x => x * p⁻¹) ⁻¹' O)) fun p =>
      interior_mem_nhds.2 ((continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds (by simpa using hO))
  have hTne : T.Nonempty := by
    have : (1 : N) ∈ ⋃ x ∈ T, interior ((fun y => y * x⁻¹) ⁻¹' O) := hT ▸ mem_univ _
    obtain ⟨p, hp, -⟩ := mem_iUnion₂.1 this
    exact ⟨p, hp⟩
  obtain ⟨p, rfl⟩ := hTc.exists_eq_range hTne
  let W : ℕ → Set N := fun i => V ∩ interior ((fun x => x * (p i)⁻¹) ⁻¹' O)
  have hWo : ∀ i, IsOpen (W i) := fun i => hV.inter isOpen_interior
  let S : ℕ → Set N := fun i => {m | ∃ l ∈ Λ, l * m ∈ W i}
  have hSo : ∀ i, IsOpen (S i) := fun i => by
    have : S i = ⋃ l ∈ Λ, (fun m => l * m) ⁻¹' W i := by ext m; simp [S]
    rw [this]
    exact isOpen_biUnion fun l _ => (hWo i).preimage (continuous_const.mul continuous_id)
  have hSi : ∀ i, ∀ l ∈ Λ, ∀ m, l * m ∈ S i ↔ m ∈ S i := fun i l hl m =>
    ⟨fun ⟨l', hl', h⟩ => ⟨l' * l, Λ.mul_mem hl' hl, by rwa [mul_assoc]⟩,
      fun ⟨l', hl', h⟩ => ⟨l' * l⁻¹, Λ.mul_mem hl' (Λ.inv_mem hl), by simpa [mul_assoc] using h⟩⟩
  have hex : ∀ m, ∃ i, m ∈ S i := fun m => by
    obtain ⟨l, hl, hlm⟩ := hcov m
    have : l * m ∈ ⋃ x ∈ range p, interior ((fun y => y * x⁻¹) ⁻¹' O) := hT ▸ mem_univ _
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := mem_iUnion₂.1 this
    exact ⟨i, l, hl, hlm, hi⟩
  refine ⟨⋃ i, W i \ ⋃ j < i, S j, MeasurableSet.iUnion fun i => (hWo i).measurableSet.diff
    (isOpen_biUnion fun j _ => hSo j).measurableSet, iUnion_subset fun i => sdiff_subset.trans inter_subset_left,
    fun m => ?_⟩
  have key : ∀ l : Λ, ∀ i, (l : N) * m ∈ W i \ ⋃ j < i, S j → i = Nat.find (hex m) := fun l i h => by
    refine ((Nat.find_eq_iff (hex m)).2 ⟨⟨l, l.2, h.1⟩, fun j hj hm => h.2 ?_⟩).symm
    exact mem_iUnion₂.2 ⟨j, hj, (hSi j l l.2 m).2 hm⟩
  obtain ⟨l, hl, hlm⟩ := Nat.find_spec (hex m)
  refine ⟨⟨l, hl⟩, mem_iUnion.2 ⟨_, hlm, fun h => ?_⟩, fun l' hl' => ?_⟩
  · obtain ⟨j, hj, hm⟩ := mem_iUnion₂.1 h
    exact Nat.find_min (hex m) hj ((hSi j l hl m).1 hm)
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hl'
    obtain rfl := key l' i hi
    have a1 := mem_preimage.1 (interior_subset hi.1.2)
    have a2 := mem_preimage.1 (interior_subset hlm.2)
    have := hinj _ a1 _ a2 (by
      simpa [mul_assoc] using Λ.mul_mem l'.2 (Λ.inv_mem hl))
    exact Subtype.ext (mul_right_cancel (mul_right_cancel this))

theorem averaging_of_fundamental_domain : FundIn → Avg := by
  intro hF G _ _ _ _ _ _ _ _ N Λ hN hle hd V hV hVc hcov
  have : LocallyCompactSpace N := hN.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  let Λ' : Subgroup N := Λ.subgroupOf N
  have hd' : Disc Λ' := fun C hC =>
    ((hd _ (hC.image continuous_subtype_val)).preimage Subtype.val_injective.injOn).subset
      fun x hx => ⟨mem_image_of_mem _ hx.1, hx.2⟩
  have := hd'.countable
  obtain ⟨D, hDm, hDV, hD⟩ := hF N Λ' hd' (Subtype.val ⁻¹' V) (hV.preimage continuous_subtype_val) fun m => by
    obtain ⟨l, hl, h⟩ := hcov m m.2
    exact ⟨⟨l, hle hl⟩, hl, h⟩
  let μ : Measure N := Measure.haar
  have hFD : ∀ g : N, IsFundamentalDomain Λ' ((fun x => x * g) ⁻¹' D) μ := fun g =>
    IsFundamentalDomain.mk' (measurable_mul_const g hDm).nullMeasurableSet fun m => by
      simpa [Subgroup.smul_def, mul_assoc] using hD (m * g)
  have hFD1 : IsFundamentalDomain Λ' D μ := by simpa using hFD 1
  have hfin : μ D ≠ ∞ := ((measure_mono (hDV.trans (preimage_mono subset_closure))).trans_lt
    (hN.isClosedEmbedding_subtypeVal.isCompact_preimage hVc).measure_lt_top).ne
  have hpos : μ D ≠ 0 := hFD1.measure_ne_zero (NeZero.ne μ)
  have hR : ∀ g : N, μ.map (fun x => x * g) = μ := fun g => by
    have h1 := Measure.isMulLeftInvariant_eq_smul (μ.map fun x => x * g) μ
    have h2 := congrArg (fun m : Measure N => m D) h1
    simp only [Measure.map_apply (measurable_mul_const g) hDm, Measure.smul_apply] at h2
    rw [(hFD g).measure_eq hFD1, ENNReal.smul_def, smul_eq_mul] at h2
    have h3 : ((μ.map fun x => x * g).haarScalarFactor μ : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj hpos hfin).1 (h2.symm.trans (one_mul _).symm)
    rw [h1, show (μ.map fun x => x * g).haarScalarFactor μ = 1 by exact_mod_cast h3, one_smul]
  have hE : MeasurableEmbedding (Subtype.val : N → G) := MeasurableEmbedding.subtype_coe hN.measurableSet
  have hP : IsProbabilityMeasure ((μ D)⁻¹ • μ.restrict D) :=
    ⟨by rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]⟩
  refine ⟨((μ D)⁻¹ • μ.restrict D).map Subtype.val, Measure.isProbabilityMeasure_map hE.measurable.aemeasurable,
    hE.ae_map_iff.2 (Measure.ae_smul_measure ((ae_restrict_mem hDm).mono fun x hx => hDV hx) _),
    fun u _ hu m₀ hm₀ y => ?_⟩
  rw [hE.integral_map, hE.integral_map, integral_smul_measure, integral_smul_measure]
  congr 1
  let g : N := ⟨m₀, hm₀⟩
  have hmp : MeasurePreserving (fun x : N => x * g⁻¹) μ μ := ⟨measurable_mul_const _, hR _⟩
  rw [← (hFD g⁻¹).setIntegral_eq hFD1 (f := fun m : N => u (m * y)) fun l x => by
      show u (((l : N) : G) * x * y) = _
      rw [mul_assoc]; exact hu _ l.2 _,
    ← hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight g⁻¹) (fun m : N => u (m * (m₀ * y))) D]
  congr 1
  funext x
  simp [g]

theorem parabolic_subgroup_decomposition : ParPi := by
  intro ι _ _ G _ _ _ i₀ N a Ht P
  refine ⟨(continuous_mulSingle i₀).comp P.cont, fun s t => by rw [P.add, Pi.mulSingle_mul], ?_,
    P.hcont.comp (continuous_apply i₀), ?_, fun t g => by simp [P.ha], ?_, fun U hU => ?_⟩
  · rintro t _ ⟨m, hm, rfl⟩
    refine ⟨_, P.norm t m hm, ?_⟩
    simp [Pi.mulSingle_mul, Pi.mulSingle_inv]
  · rintro _ ⟨m, hm, rfl⟩ g
    simp [P.hN m hm]
  · obtain ⟨c, hc, hb⟩ := P.bd
    exact ⟨fun y => c (y i₀), hc.comp (continuous_apply i₀), fun x y => hb _ _⟩
  · obtain ⟨τ, hτ, h⟩ := P.small (Pi.mulSingle i₀ ⁻¹' U)
      ((continuous_mulSingle i₀).continuousAt.preimage_mem_nhds (by simpa using hU))
    refine ⟨τ, hτ, fun t ht x => ?_⟩
    obtain ⟨m, hm, hx⟩ := h t ht (x i₀)
    refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
    refine (congrArg (· ∈ U) ?_).mpr (mem_preimage.1 hx)
    funext i
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [Pi.mulSingle_eq_of_ne hi]

end CompanionTheory.D.gk.RF
