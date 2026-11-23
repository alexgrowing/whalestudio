import Mathlib

noncomputable section

namespace GroundTheory.Heights₂.Theta

open MeasureTheory Measure Filter Topology Set
open scoped NNReal ENNReal Pointwise

section Field

variable {R : Type*} [Field R] [TopologicalSpace R] [IsTopologicalRing R]

def mulLeftAddEquiv (a : R) (ha : a ≠ 0) : R ≃ₜ+ R where
  toFun x := a * x
  invFun x := a⁻¹ * x
  left_inv x := inv_mul_cancel_left₀ ha x
  right_inv x := mul_inv_cancel_left₀ ha x
  map_add' x y := mul_add a x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem mulLeftAddEquiv_apply (a : R) (ha : a ≠ 0) (x : R) : mulLeftAddEquiv a ha x = a * x := rfl

theorem mulLeftAddEquiv_mul (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    mulLeftAddEquiv (a * b) (mul_ne_zero ha hb) =
      (mulLeftAddEquiv b hb).trans (mulLeftAddEquiv a ha) := by
  ext x
  simp [mulLeftAddEquiv_apply, mul_assoc]

theorem nhdsNE_zero_neBot (hR : ¬ DiscreteTopology R) : (𝓝[≠] (0 : R)).NeBot := by
  by_contra h
  rw [not_neBot, ← isOpen_singleton_iff_punctured_nhds] at h
  exact hR (discreteTopology_iff_isOpen_singleton_zero.mpr h)

theorem eventually_mul_mem_of_isCompact {K N : Set R} (hK : IsCompact K) (hN : N ∈ 𝓝 (0 : R)) :
    ∀ᶠ u in 𝓝 (0 : R), ∀ w ∈ K, u * w ∈ N := by
  apply hK.eventually_forall_of_forall_eventually
  intro w _
  have h : Tendsto (fun z : R × R => z.1 * z.2) (𝓝 (0, w)) (𝓝 (0 * w)) :=
    continuous_mul.tendsto _
  rw [zero_mul] at h
  exact h.eventually_mem hN

variable [LocallyCompactSpace R] [T2Space R]

theorem exists_tendsto_pow_zero (hR : ¬ DiscreteTopology R) :
    ∃ t : R, t ≠ 0 ∧ Tendsto (fun n : ℕ => t ^ n) atTop (𝓝 0) := by
  let _ : MeasurableSpace R := borel R
  have _ : BorelSpace R := ⟨rfl⟩
  have _ := nhdsNE_zero_neBot hR
  let ν : Measure R := addHaar

  let md : ∀ a : R, a ≠ 0 → ℝ≥0 := fun a ha => addEquivAddHaarChar (mulLeftAddEquiv a ha)
  have md_image : ∀ (a : R) (ha : a ≠ 0) (S : Set R),
      ν ((fun x => a * x) '' S) = (md a ha : ℝ≥0∞) * ν S := by
    intro a ha S
    have h := addEquivAddHaarChar_smul_preimage ν (X := (fun x => a * x) '' S)
      (mulLeftAddEquiv a ha)
    have hpre : (mulLeftAddEquiv a ha) ⁻¹' ((fun x => a * x) '' S) = S :=
      preimage_image_eq S (mulLeftAddEquiv a ha).injective
    rw [hpre, ENNReal.smul_def, smul_eq_mul] at h
    exact h.symm
  have md_pos : ∀ (a : R) (ha : a ≠ 0), 0 < md a ha := fun a ha => addEquivAddHaarChar_pos _
  have md_mul : ∀ (a b : R) (ha : a ≠ 0) (hb : b ≠ 0),
      md (a * b) (mul_ne_zero ha hb) = md b hb * md a ha := by
    intro a b ha hb
    simp only [md]
    rw [mulLeftAddEquiv_mul a b ha hb, addEquivAddHaarChar_trans]
  have md_pow : ∀ (a : R) (ha : a ≠ 0) (n : ℕ), md (a ^ n) (pow_ne_zero n ha) = md a ha ^ n := by
    intro a ha n
    induction n with
    | zero =>
      simp only [md, pow_zero]
      have : mulLeftAddEquiv (1 : R) one_ne_zero = ContinuousAddEquiv.refl R := by
        ext x; simp [mulLeftAddEquiv_apply]
      rw [this, addEquivAddHaarChar_refl]
    | succ n ih =>
      have h := md_mul (a ^ n) a (pow_ne_zero n ha) ha
      simp only [← pow_succ] at h
      rw [h, ih, pow_succ, mul_comm]

  obtain ⟨V0, hV0c, hV0n⟩ : ∃ V0 : Set R, IsCompact V0 ∧ V0 ∈ 𝓝 (0 : R) :=
    exists_compact_mem_nhds 0
  set W : Set R := insert 1 V0 with hWdef
  have hWc : IsCompact W := hV0c.insert 1
  have hWn : W ∈ 𝓝 (0 : R) := mem_of_superset hV0n (subset_insert _ _)
  have h1W : (1 : R) ∈ W := mem_insert _ _
  have hWpos : 0 < ν W := measure_pos_of_mem_nhds ν hWn
  have hWfin : ν W ≠ ∞ := hWc.measure_lt_top.ne
  have hV0pos : 0 < ν V0 := measure_pos_of_mem_nhds ν hV0n
  obtain ⟨O, hOsup, hOo, hOlt⟩ := Set.exists_isOpen_lt_of_lt ({0} : Set R) (ν V0)
    (by rw [measure_singleton (μ := ν) (0 : R)]; exact hV0pos)
  obtain ⟨V, hVn, hVsub, hVc⟩ := local_compact_nhds
    (inter_mem (hOo.mem_nhds (hOsup rfl)) hV0n)
  have hVW : V ⊆ W := fun x hx => subset_insert _ _ (hVsub hx).2
  have hVO : ν V < ν W :=
    ((measure_mono fun x hx => (hVsub hx).1).trans_lt hOlt).trans_le
      (measure_mono (subset_insert _ _))

  obtain ⟨t, htV, ht0⟩ := ((eventually_mul_mem_of_isCompact hWc hVn).filter_mono
    nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ({0}ᶜ : Set R) ∈ 𝓝[≠] (0 : R)) |>.exists
  have ht0' : t ≠ 0 := ht0
  have hmd_t : md t ht0' < 1 := by
    have h1 : ν ((fun x => t * x) '' W) ≤ ν V :=
      measure_mono (by rintro _ ⟨w, hw, rfl⟩; exact htV w hw)
    rw [md_image] at h1
    have h2 : (md t ht0' : ℝ≥0∞) * ν W < 1 * ν W := by rw [one_mul]; exact h1.trans_lt hVO
    have h3 := (ENNReal.mul_lt_mul_iff_left hWpos.ne' hWfin).mp h2
    exact_mod_cast h3

  let S : ℕ → Set R := fun n => (fun x => t ^ n * x) '' W
  have hSc : ∀ n, IsCompact (S n) := fun n => hWc.image (continuous_const.mul continuous_id)
  have hSanti : Antitone S := by
    apply antitone_nat_of_succ_le
    intro n
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨t * w, hVW (htV w hw), by simp only [pow_succ, mul_assoc]⟩
  have hSmem : ∀ n, t ^ n ∈ S n := fun n => ⟨1, h1W, mul_one _⟩

  set C : Set R := (fun p : R × R => p.1 * p.2) '' (W ×ˢ W)
  have hCfin : ν C ≠ ∞ := ((hWc.prod hWc).image continuous_mul).measure_lt_top.ne
  have hinter : ∀ a ∈ ⋂ n, S n, a = 0 := by
    intro a ha
    by_contra ha0
    have key : ∀ n : ℕ, (md a ha0 : ℝ≥0∞) * ν W ≤ (md t ht0' : ℝ≥0∞) ^ n * ν C := by
      intro n
      obtain ⟨w, hw, hwa⟩ := mem_iInter.mp ha n
      have hw0 : w ≠ 0 := by
        rintro rfl
        simp only [mul_zero] at hwa
        exact ha0 hwa.symm
      have hmd : md a ha0 = md w hw0 * md t ht0' ^ n := by
        have := md_mul (t ^ n) w (pow_ne_zero n ht0') hw0
        simp only [hwa] at this
        rw [this, md_pow]
      have hsub : (fun x => w * x) '' W ⊆ C := by
        rintro _ ⟨x, hx, rfl⟩; exact ⟨(w, x), ⟨hw, hx⟩, rfl⟩
      calc (md a ha0 : ℝ≥0∞) * ν W
          = (md t ht0' : ℝ≥0∞) ^ n * ((md w hw0 : ℝ≥0∞) * ν W) := by
            rw [hmd]; push_cast; ring
        _ = (md t ht0' : ℝ≥0∞) ^ n * ν ((fun x => w * x) '' W) := by rw [md_image]
        _ ≤ (md t ht0' : ℝ≥0∞) ^ n * ν C := by gcongr
    have hlim : Tendsto (fun n : ℕ => (md t ht0' : ℝ≥0∞) ^ n * ν C) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_pow_atTop_nhds_zero_iff.mpr (ENNReal.coe_lt_one_iff.mpr hmd_t))
        (Or.inr hCfin) (a := 0) (b := ν C)
      rwa [zero_mul] at h
    have hle := ge_of_tendsto' hlim key
    have hpos : 0 < (md a ha0 : ℝ≥0∞) * ν W :=
      ENNReal.mul_pos (by exact_mod_cast (md_pos a ha0).ne') hWpos.ne'
    exact absurd hle (not_le.mpr hpos)
  refine ⟨t, ht0', ?_⟩
  intro U hU
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact hSanti.directed_ge hSc
    (U := U) (fun x hx => by rw [hinter x hx]; exact hU)
  rw [mem_map, mem_atTop_sets]
  exact ⟨n, fun m hm => hn (hSanti hm (hSmem m))⟩

theorem locField_sigmaCompactSpace (hR : ¬ DiscreteTopology R) : SigmaCompactSpace R := by
  obtain ⟨t, ht0, ht⟩ := exists_tendsto_pow_zero hR
  obtain ⟨W, hWc, hWn⟩ : ∃ W : Set R, IsCompact W ∧ W ∈ 𝓝 (0 : R) := exists_compact_mem_nhds 0
  refine ⟨⟨fun n => (fun x => (t ^ n)⁻¹ * x) '' W,
    fun n => hWc.image (continuous_const.mul continuous_id), ?_⟩⟩
  apply eq_univ_of_forall
  intro x
  have h : Tendsto (fun n : ℕ => t ^ n * x) atTop (𝓝 0) := by
    have := ht.mul_const x
    rwa [zero_mul] at this
  obtain ⟨n, hn⟩ := (h.eventually_mem hWn).exists
  exact mem_iUnion.mpr ⟨n, t ^ n * x, hn, inv_mul_cancel_left₀ (pow_ne_zero n ht0) x⟩

theorem locField_nhds_zero_isCountablyGenerated (hR : ¬ DiscreteTopology R) :
    (𝓝 (0 : R)).IsCountablyGenerated := by
  obtain ⟨t, ht0, ht⟩ := exists_tendsto_pow_zero hR
  obtain ⟨W, hWc, hWn⟩ : ∃ W : Set R, IsCompact W ∧ W ∈ 𝓝 (0 : R) := exists_compact_mem_nhds 0
  have hb : (𝓝 (0 : R)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => t ^ n * x) '' W) := by
    refine ⟨fun U => ⟨fun hU => ?_, ?_⟩⟩
    · obtain ⟨n, hn⟩ := (ht.eventually (eventually_mul_mem_of_isCompact hWc hU)).exists
      exact ⟨n, trivial, by rintro _ ⟨w, hw, rfl⟩; exact hn w hw⟩
    · rintro ⟨n, -, hn⟩
      apply mem_of_superset _ hn
      have h := (mulLeftAddEquiv (t ^ n) (pow_ne_zero n ht0)).toHomeomorph.isOpenMap.image_mem_nhds
        hWn
      have e1 : ((mulLeftAddEquiv (t ^ n) (pow_ne_zero n ht0)).toHomeomorph : R → R) =
          fun x => t ^ n * x := rfl
      rw [e1] at h
      simpa only [mul_zero] using h
  exact hb.isCountablyGenerated

theorem locField_secondCountable (hR : ¬ DiscreteTopology R) : SecondCountableTopology R := by
  have _ := locField_sigmaCompactSpace hR
  have _ := locField_nhds_zero_isCountablyGenerated hR
  let _ := IsTopologicalAddGroup.rightUniformSpace R
  have _ := isUniformAddGroup_of_addCommGroup (G := R)
  have _ : (uniformity R).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have _ : TopologicalSpace.MetrizableSpace R := UniformSpace.metrizableSpace
  let _ := TopologicalSpace.metrizableSpaceMetric R
  exact EMetric.secondCountable_of_sigmaCompact R

end Field

section Module

variable {R : Type*} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
  {X : Type*} [AddCommGroup X] [Module R X] [FiniteDimensional R X] [TopologicalSpace X]
  [IsModuleTopology R X]

variable (R X) in

def coordHomeomorph : X ≃ₜ (Fin (Module.finrank R X) → R) :=
  haveI := IsModuleTopology.toContinuousAdd R X
  { toEquiv := (Module.finBasis R X).equivFun.toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Module.finBasis R X).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Module.finBasis R X).equivFun.symm.toLinearMap }

end Module

section Haar

theorem isAddHaar_regular {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] : μ.Regular := by
  have h : μ = addHaarScalarFactor μ addHaar • addHaar := by
    ext s _
    have hs : s = ⋃ n, s ∩ compactCovering G n := by
      rw [← inter_iUnion, iUnion_compactCovering, inter_univ]
    have hmono : Monotone (fun n => s ∩ compactCovering G n) :=
      fun m n hmn => inter_subset_inter_right _ (compactCovering_subset G hmn)
    rw [hs, hmono.measure_iUnion, hmono.measure_iUnion]
    congr 1
    funext n
    rw [Measure.smul_apply]
    exact measure_isAddInvariant_eq_smul_of_isCompact_closure μ addHaar
      ((isCompact_compactCovering G n).closure_of_subset inter_subset_right)
  rw [h]
  infer_instance

end Haar

end GroundTheory.Heights₂.Theta
