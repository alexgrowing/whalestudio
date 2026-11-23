import Mathlib

open MeasureTheory Measure Topology Set Function TopologicalSpace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace HaarSK

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def mulMap (S K : Subgroup G) (p : S × K) : G := (p.1 : G) * (p.2 : G)

variable {S K : Subgroup G}

theorem continuous_mulMap : Continuous (mulMap S K) :=
  (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

section Topology

variable [T2Space G] (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G))
include hS hK

theorem isCompact_preimage_mulMap {C : Set G} (hC : IsCompact C) :
    IsCompact (mulMap S K ⁻¹' C) := by
  have hA : IsCompact ((fun q : G × G => q.1 * q.2⁻¹) '' (C ×ˢ (K : Set G))) :=
    (hC.prod hK).image (continuous_fst.mul continuous_snd.inv)
  have hA' := hS.isClosedEmbedding_subtypeVal.isCompact_preimage hA
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine (hA'.prod isCompact_univ).of_isClosed_subset
    (hC.isClosed.preimage continuous_mulMap) ?_
  rintro ⟨s, k⟩ h
  refine ⟨⟨((s : G) * k, (k : G)), ⟨h, k.2⟩, ?_⟩, mem_univ _⟩
  simp

variable [LocallyCompactSpace G]

theorem isProperMap_mulMap : IsProperMap (mulMap S K) :=
  isProperMap_iff_isCompact_preimage.2
    ⟨continuous_mulMap, fun _ hC => isCompact_preimage_mulMap hS hK hC⟩

theorem isQuotientMap_mulMap (hSK : Surjective (mulMap S K)) : IsQuotientMap (mulMap S K) :=
  (isProperMap_mulMap hS hK).isClosedMap.isQuotientMap continuous_mulMap hSK

end Topology

abbrev inter (S K : Subgroup G) : Subgroup S := K.subgroupOf S

theorem mem_inter_iff {m : S} : m ∈ inter S K ↔ (m : G) ∈ K := Subgroup.mem_subgroupOf

theorem exists_mem_inter_of_mul_eq {s s' : S} {k k' : K} (h : (s : G) * k = (s' : G) * k') :
    ∃ m ∈ inter S K, s' = s * m := by
  refine ⟨s⁻¹ * s', ?_, by group⟩
  rw [mem_inter_iff]
  have : ((s⁻¹ * s' : S) : G) = (k : G) * (k' : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h]; group
  rw [this]
  exact K.mul_mem k.2 (K.inv_mem k'.2)

variable (hSK : Surjective (mulMap S K))

def lift (u : S → ℝ) (g : G) : ℝ := u (hSK.hasRightInverse.choose g).1

variable {hSK}

theorem lift_mulMap {u : S → ℝ} (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s) (p : S × K) :
    lift hSK u (mulMap S K p) = u p.1 := by
  set q := hSK.hasRightInverse.choose (mulMap S K p)
  have hq : mulMap S K q = mulMap S K p := hSK.hasRightInverse.choose_spec _
  obtain ⟨m, hm, he⟩ := exists_mem_inter_of_mul_eq (s := p.1) (s' := q.1) (k := p.2) (k' := q.2)
    hq.symm
  change u q.1 = u p.1
  rw [he, hu _ _ hm]

theorem lift_mul {u : S → ℝ} (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s) (s : S) (k : K) :
    lift hSK u ((s : G) * k) = u s :=
  lift_mulMap hu (s, k)

theorem lift_add (u w : S → ℝ) : lift hSK (u + w) = lift hSK u + lift hSK w := rfl

theorem lift_smul (c : ℝ) (u : S → ℝ) : lift hSK (c • u) = c • lift hSK u := rfl

section Measure

variable [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G]

def flat (mL : Measure (inter S K)) (v : S → ℝ) (s : S) : ℝ := ∫ m, v (s * m) ∂mL

variable {mL : Measure (inter S K)}

theorem flat_mul_inter [mL.IsMulLeftInvariant] (v : S → ℝ) (s : S) (m : inter S K) :
    flat mL v (s * m) = flat mL v s := by
  unfold flat
  have := integral_mul_left_eq_self (μ := mL) (fun m' : inter S K => v (s * m')) m
  simpa only [Subgroup.coe_mul, mul_assoc] using this

theorem flat_right_inv [mL.IsMulLeftInvariant] (v : S → ℝ) :
    ∀ s, ∀ m ∈ inter S K, flat mL v (s * m) = flat mL v s :=
  fun s m hm => flat_mul_inter v s ⟨m, hm⟩

theorem flat_eq_self [IsProbabilityMeasure mL] {u : S → ℝ}
    (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s) : flat mL u = u := by
  funext s
  simp only [flat]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun m : inter S K => hu s m m.2)]
  simp

variable [LocallyCompactSpace S] [CompactSpace (inter S K)]

theorem integrable_mul_inter [IsFiniteMeasure mL] {v : S → ℝ} (hv : Continuous v) (s : S) :
    Integrable (fun m : inter S K => v (s * m)) mL :=
  (hv.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

theorem continuous_flat [IsFiniteMeasure mL] {v : S → ℝ} (hv : Continuous v) :
    Continuous (flat mL v) := by
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  show Continuous fun s : S => ∫ m, v (s * m) ∂mL
  have := continuous_parametric_integral_of_continuous (μ := mL)
    (f := fun (s : S) (m : inter S K) => v (s * m))
    (hv.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))) isCompact_univ
  simpa [flat] using this

theorem hasCompactSupport_flat {v : S → ℝ} (hv : HasCompactSupport v) :
    HasCompactSupport (flat mL v) := by
  refine HasCompactSupport.intro
    ((IsCompact.prod hv (isCompact_univ (X := inter S K))).image
      (f := fun p : S × inter S K => p.1 * (p.2 : S)⁻¹) (by fun_prop)) ?_
  intro s hs
  have h0 : ∀ m : inter S K, v (s * m) = 0 := fun m => by
    by_contra h
    exact hs ⟨(s * m, m), ⟨subset_tsupport _ h, mem_univ _⟩, by simp⟩
  simp [flat, h0]

theorem flat_add [IsFiniteMeasure mL] (v w : CompactlySupportedContinuousMap S ℝ) :
    flat mL (⇑(v + w)) = flat mL v + flat mL w := by
  funext s
  simp only [flat, CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
  exact integral_add (integrable_mul_inter v.continuous s) (integrable_mul_inter w.continuous s)

theorem flat_smul (c : ℝ) (v : CompactlySupportedContinuousMap S ℝ) :
    flat mL (⇑(c • v)) = c • flat mL v := by
  funext s
  change ∫ m, (c • v) (s * m) ∂mL = c • ∫ m, v (s * m) ∂mL
  rw [smul_eq_mul, ← integral_const_mul]
  rfl

variable (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G)) (hSK : Surjective (mulMap S K))
include hS hK

theorem continuous_lift {u : S → ℝ} (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s)
    (huc : Continuous u) : Continuous (lift hSK u) := by
  rw [(isQuotientMap_mulMap hS hK hSK).continuous_iff]
  have : lift hSK u ∘ mulMap S K = u ∘ Prod.fst := funext fun p => lift_mulMap hu p
  rw [this]
  exact huc.comp continuous_fst

theorem hasCompactSupport_lift {u : S → ℝ} (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s)
    (hcs : HasCompactSupport u) : HasCompactSupport (lift hSK u) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine HasCompactSupport.intro ((IsCompact.prod hcs (isCompact_univ (X := K))).image
    continuous_mulMap) ?_
  intro g hg
  obtain ⟨p, rfl⟩ := hSK g
  rw [lift_mulMap hu]
  by_contra h
  exact hg ⟨p, ⟨subset_tsupport _ h, mem_univ _⟩, rfl⟩

variable (mL) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasure mL]
  [mL.IsMulLeftInvariant]

theorem integrable_lift_flat (v : CompactlySupportedContinuousMap S ℝ) :
    Integrable (lift hSK (flat mL v)) μ :=
  (continuous_lift hS hK hSK (flat_right_inv _) (continuous_flat v.continuous)).integrable_of_hasCompactSupport
    (hasCompactSupport_lift hS hK hSK (flat_right_inv _) (hasCompactSupport_flat v.hasCompactSupport))

def funcL : CompactlySupportedContinuousMap S ℝ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun v => ∫ g, lift hSK (flat mL v) g ∂μ
      map_add' := fun v w => by
        rw [flat_add, lift_add]
        exact integral_add (integrable_lift_flat mL hS hK hSK μ v)
          (integrable_lift_flat mL hS hK hSK μ w)
      map_smul' := fun c v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [flat_smul, lift_smul]
        exact integral_const_mul c _ }
    (fun v hv => integral_nonneg fun g => integral_nonneg fun m => hv _)

theorem funcL_apply (v : CompactlySupportedContinuousMap S ℝ) :
    funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) v = ∫ g, lift hSK (flat mL v) g ∂μ := rfl

end Measure

section Main

variable [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G]

def translate (s₀ : S) (v : CompactlySupportedContinuousMap S ℝ) :
    CompactlySupportedContinuousMap S ℝ where
  toFun s := v (s₀ * s)
  continuous_toFun := v.continuous.comp (continuous_const.mul continuous_id)
  hasCompactSupport' := v.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft s₀)

theorem translate_apply (s₀ : S) (v : CompactlySupportedContinuousMap S ℝ) (s : S) :
    translate s₀ v s = v (s₀ * s) := rfl

variable {mL : Measure (inter S K)} [LocallyCompactSpace S] [CompactSpace (inter S K)]
  [IsFiniteMeasure mL] [mL.IsMulLeftInvariant]
  {hS : IsClosed (S : Set G)} {hK : IsCompact (K : Set G)} {hSK : Surjective (mulMap S K)}
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

theorem lift_flat_translate (s₀ : S) (v : CompactlySupportedContinuousMap S ℝ) (g : G) :
    lift hSK (flat mL (translate s₀ v)) g = lift hSK (flat mL v) ((s₀ : G) * g) := by
  obtain ⟨p, rfl⟩ := hSK g
  rw [lift_mulMap (flat_right_inv _) p]
  have : (s₀ : G) * mulMap S K p = mulMap S K (s₀ * p.1, p.2) := by
    simp [mulMap, mul_assoc]
  rw [this, lift_mulMap (flat_right_inv _)]
  simp only [flat, translate_apply, mul_assoc]

theorem funcL_translate (s₀ : S) (v : CompactlySupportedContinuousMap S ℝ) :
    funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) (translate s₀ v) =
      funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) v := by
  rw [funcL_apply, funcL_apply]
  simp_rw [lift_flat_translate]
  exact integral_mul_left_eq_self (fun g => lift hSK (flat mL v) g) (s₀ : G)

variable (mL hS hK hSK μ)

abbrev rmk : Measure S := RealRMK.rieszMeasure (funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ))

theorem integral_rmk (v : CompactlySupportedContinuousMap S ℝ) :
    ∫ s, v s ∂rmk mL hS hK hSK μ = funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) v :=
  RealRMK.integral_rieszMeasure _ v

theorem isMulLeftInvariant_rmk : (rmk mL hS hK hSK μ).IsMulLeftInvariant := by
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  constructor
  intro s₀
  have : IsFiniteMeasureOnCompacts (map (s₀ * ·) (rmk mL hS hK hSK μ)) :=
    IsFiniteMeasureOnCompacts.map _ (Homeomorph.mulLeft s₀)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro v
  rw [integral_map (measurable_const_mul s₀).aemeasurable (map_continuous v).aestronglyMeasurable]
  have h := integral_rmk mL hS hK hSK μ (translate s₀ v)
  rw [funcL_translate, ← integral_rmk] at h
  exact h

end Main

theorem exists_eq_smul_map_mulMap [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G)) (hSK : Surjective (mulMap S K))
    (μS : Measure S) [μS.IsHaarMeasure] (μK : Measure K) [μK.IsHaarMeasure] :
    ∃ c : ℝ≥0, μ = c • map (mulMap S K) (μS.prod μK) := by
  have : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hLc : IsCompact ((inter S K : Subgroup S) : Set S) := by
    rw [Subgroup.coe_subgroupOf]
    exact hS.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have : CompactSpace (inter S K) := isCompact_iff_compactSpace.mp hLc
  set mL : Measure (inter S K) := haarMeasure ⊤ with hmL
  have : IsProbabilityMeasure mL := ⟨by simpa using haarMeasure_self (K₀ := (⊤ : PositiveCompacts (inter S K)))⟩
  have : (rmk mL hS hK hSK μ).IsMulLeftInvariant := isMulLeftInvariant_rmk mL hS hK hSK μ
  set c₀ := haarScalarFactor (rmk mL hS hK hSK μ) μS
  have hc₀ : rmk mL hS hK hSK μ = c₀ • μS := isMulLeftInvariant_eq_smul _ _
  have : IsFiniteMeasure μK := inferInstance
  have hKpos : 0 < (μK univ).toReal :=
    ENNReal.toReal_pos (IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty)
      (measure_ne_top _ _)

  have hfin : IsFiniteMeasureOnCompacts (map (mulMap S K) (μS.prod μK)) := ⟨fun C hC => by
    rw [map_apply continuous_mulMap.measurable hC.measurableSet]
    exact (isCompact_preimage_mulMap hS hK hC).measure_lt_top⟩
  have key : ∀ φ : CompactlySupportedContinuousMap G ℝ,
      (μK univ).toReal * ∫ g, φ g ∂μ = (c₀ : ℝ) * ∫ p, φ (mulMap S K p) ∂(μS.prod μK) := by
    intro φ
    set φK : G → ℝ := fun g => ∫ k, φ (g * k) ∂μK with hφK
    have hφKc : Continuous φK := by
      have := continuous_parametric_integral_of_continuous (μ := μK)
        (f := fun (g : G) (k : K) => φ (g * k))
        (φ.continuous.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
        isCompact_univ
      simpa using this
    have hφKinv : ∀ g (k : K), φK (g * k) = φK g := by
      intro g k
      simp only [hφK]
      have := integral_mul_left_eq_self (μ := μK) (fun k' : K => φ (g * k')) k
      simpa only [Subgroup.coe_mul, mul_assoc] using this
    have hφKcs : HasCompactSupport φK := by
      refine HasCompactSupport.intro ((IsCompact.prod φ.hasCompactSupport hK).image
        (f := fun q : G × G => q.1 * q.2⁻¹) (by fun_prop)) ?_
      intro g hg
      have h0 : ∀ k : K, φ (g * k) = 0 := fun k => by
        by_contra h
        exact hg ⟨(g * k, k), ⟨subset_tsupport _ h, k.2⟩, by simp⟩
      simp [hφK, h0]

    have hint : ∫ g, φK g ∂μ = (μK univ).toReal * ∫ g, φ g ∂μ := by
      have hF : Integrable (fun q : G × K => φ (q.1 * q.2)) (μ.prod μK) := by
        refine (φ.continuous.comp (continuous_fst.mul (continuous_subtype_val.comp
          continuous_snd))).integrable_of_hasCompactSupport ?_
        refine HasCompactSupport.intro (((IsCompact.prod φ.hasCompactSupport hK).image
          (f := fun q : G × G => q.1 * q.2⁻¹) (by fun_prop)).prod (isCompact_univ (X := K))) ?_
        rintro ⟨g, k⟩ hq
        by_contra h
        exact hq ⟨⟨(g * k, k), ⟨subset_tsupport _ h, k.2⟩, by simp⟩, mem_univ _⟩
      rw [hφK, integral_integral_swap hF]
      simp_rw [integral_mul_right_eq_self (μ := μ) (fun g => φ g)]
      rw [integral_const, smul_eq_mul, measureReal_def]

    have hu : ∀ s, ∀ m ∈ inter S K, (fun s : S => φK s) (s * m) = (fun s : S => φK s) s := by
      intro s m hm
      simpa using hφKinv (s : G) ⟨(m : G), (mem_inter_iff).1 hm⟩
    set uCc : CompactlySupportedContinuousMap S ℝ :=
      { toFun := fun s => φK s
        continuous_toFun := hφKc.comp continuous_subtype_val
        hasCompactSupport' := hφKcs.comp_isClosedEmbedding hS.isClosedEmbedding_subtypeVal }
    have hflat : flat mL uCc = fun s : S => φK (s : G) := flat_eq_self (u := fun s : S => φK (s : G)) hu
    have hlift : lift hSK (flat mL uCc) = φK := by
      rw [hflat]
      funext g
      obtain ⟨p, rfl⟩ := hSK g
      rw [lift_mulMap hu]
      exact (hφKinv _ _).symm
    have h1 := integral_rmk mL hS hK hSK μ uCc
    rw [funcL_apply, hlift, hint, hc₀, integral_smul_nnreal_measure] at h1
    rw [← h1]
    have hFS : Integrable (fun p : S × K => φ (mulMap S K p)) (μS.prod μK) :=
      (φ.continuous.comp continuous_mulMap).integrable_of_hasCompactSupport
        (isCompact_preimage_mulMap hS hK φ.hasCompactSupport |>.of_isClosed_subset
          (isClosed_tsupport _) (by
            intro p hp
            exact (tsupport_comp_subset_preimage φ continuous_mulMap) hp))
    rw [integral_prod _ hFS]
    rfl
  set c : ℝ≥0 := ⟨c₀ / (μK univ).toReal, div_nonneg c₀.2 hKpos.le⟩ with hc
  refine ⟨c, ?_⟩
  have hreg : (map (mulMap S K) (μS.prod μK)).Regular := inferInstance
  have : (c • map (mulMap S K) (μS.prod μK)).Regular := by
    rw [ENNReal.smul_def]
    exact Measure.Regular.smul ENNReal.coe_ne_top
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [integral_smul_nnreal_measure, integral_map continuous_mulMap.aemeasurable
    (map_continuous φ).aestronglyMeasurable, NNReal.smul_def, smul_eq_mul]
  show _ = ((c₀ : ℝ) / (μK univ).toReal) * _
  rw [div_mul_eq_mul_div, ← key, mul_div_cancel_left₀ _ hKpos.ne']

theorem exists_lintegral_eq [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G)) (hSK : Surjective (mulMap S K))
    (μS : Measure S) [μS.IsHaarMeasure] (μK : Measure K) [μK.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = c * ∫⁻ s, ∫⁻ k, f ((s : G) * k) ∂μK ∂μS := by
  obtain ⟨c, hc⟩ := exists_eq_smul_map_mulMap μ hS hK hSK μS μK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  have hform : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = c * ∫⁻ s, ∫⁻ k, f ((s : G) * k) ∂μK ∂μS := by
    intro f hf
    rw [hc, lintegral_smul_measure, lintegral_map hf continuous_mulMap.measurable,
      lintegral_prod (fun p : S × K => f (mulMap S K p))
        (hf.comp continuous_mulMap.measurable).aemeasurable, ENNReal.smul_def,
      smul_eq_mul]
    rfl
  refine ⟨c, fun h0 => ?_, hform⟩
  have h1 := hform 1 measurable_const
  rw [h0, ENNReal.coe_zero, zero_mul] at h1
  simp only [Pi.one_apply, lintegral_const, one_mul] at h1
  exact (IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty) h1

end HaarSK

end

end GroundTheory.Automorphic
