import Mathlib
import Formalism.UnipotentAdelicQuotients.HaarProductClosedCompact

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.HaarPK

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

theorem exists_eq_smul [LocallyCompactSpace G] [SecondCountableTopology G] (μ ν : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (hμ : μ ≠ 0) (hν : ν ≠ 0) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts G) := inferInstance
  have h1 := Measure.haarMeasure_unique μ K₀
  have h2 := Measure.haarMeasure_unique ν K₀
  have a0 : μ K₀ ≠ 0 := fun h => hμ (by rw [h1, h, zero_smul])
  have b0 : ν K₀ ≠ 0 := fun h => hν (by rw [h2, h, zero_smul])
  have at' : μ K₀ ≠ ⊤ := K₀.isCompact.measure_lt_top.ne
  have bt : ν K₀ ≠ ⊤ := K₀.isCompact.measure_lt_top.ne
  refine ⟨μ K₀ / ν K₀, ENNReal.div_ne_zero.2 ⟨a0, bt⟩, ENNReal.div_ne_top at' b0, ?_⟩
  conv_lhs => rw [h1]
  conv_rhs => rw [h2]
  rw [smul_smul, ← h2, ENNReal.div_mul_cancel b0 bt]

theorem map_mul_right_eq [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (hμ : μ ≠ 0) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : μ.map (fun x => x * k) = μ := by
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts G) := inferInstance
  have h1 := Measure.haarMeasure_unique μ K₀
  have a0 : μ K₀ ≠ 0 := fun h => hμ (by rw [h1, h, zero_smul])
  haveI : IsFiniteMeasureOnCompacts (μ.map (fun x => x * k)) :=
    ⟨fun C hC => by
      rw [Measure.map_apply (measurable_mul_const k) hC.measurableSet]
      exact ((Homeomorph.mulRight k).isCompact_preimage.2 hC).measure_lt_top⟩
  have hne : μ.map (fun x => x * k) ≠ 0 := by
    rwa [Ne, Measure.map_eq_zero_iff (measurable_mul_const k).aemeasurable]
  obtain ⟨c, -, -, hc⟩ := exists_eq_smul (μ.map (fun x => x * k)) μ hne hμ
  have hC : IsCompact ((K₀ : Set G) * (K : Set G)) := K₀.isCompact.mul hK
  have hpre : (fun x => x * k) ⁻¹' ((K₀ : Set G) * (K : Set G)) = (K₀ : Set G) * (K : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), by
        simp only at hab ⊢; rw [← mul_assoc, hab]; simp⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨a, ha, b * k, K.mul_mem hb hk, by
        simp only at hab ⊢; rw [← mul_assoc, hab]⟩
  have h0 : μ ((K₀ : Set G) * (K : Set G)) ≠ 0 := fun h =>
    a0 (measure_mono_null (fun x hx => Set.mem_mul.2 ⟨x, hx, 1, K.one_mem, mul_one x⟩) h)
  have h2 := congrArg (fun m : Measure G => m ((K₀ : Set G) * (K : Set G))) hc
  simp only [Measure.smul_apply, smul_eq_mul] at h2
  rw [Measure.map_apply (measurable_mul_const k) hC.measurableSet, hpre] at h2
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hC.measure_lt_top.ne).1 ((one_mul _).trans h2)
    exact this.symm
  rw [hc, hc1, one_smul]

def transl (M : Subgroup G) (η : Measure M) (x : G) : Measure G := η.map (fun m : M => x * m)

theorem measurable_transl_fun (M : Subgroup G) (x : G) : Measurable (fun m : M => x * (m : G)) :=
  measurable_subtype_coe.const_mul x

theorem transl_mul_mem (M : Subgroup G) (η : Measure M) [η.IsMulLeftInvariant] (x : G) {m : G} (hm : m ∈ M) :
    transl M η (x * m) = transl M η x := by
  unfold transl
  conv_rhs => rw [← map_mul_left_eq_self η ⟨m, hm⟩]
  rw [Measure.map_map (measurable_transl_fun M x) (measurable_const_mul _)]
  congr 1
  ext y
  simp [mul_assoc]

theorem transl_mul (M : Subgroup G) (η : Measure M) (q x : G) :
    transl M η (q * x) = (transl M η x).map (fun y => q * y) := by
  unfold transl
  rw [Measure.map_map (measurable_const_mul _) (measurable_transl_fun M x)]
  congr 1
  ext y
  simp [mul_assoc]

theorem isClosed_transl_le (M : Subgroup G) (η : Measure M) [η.Regular] {U : Set G} (hU : IsOpen U) (t : ℝ≥0∞) :
    IsClosed {x | transl M η x U ≤ t} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_setOf_eq, not_le, transl] at hx
  rw [Measure.map_apply (measurable_transl_fun M x) hU.measurableSet] at hx
  have hopen : IsOpen ((fun m : M => x * (m : G)) ⁻¹' U) := hU.preimage (by fun_prop)
  obtain ⟨C, hCU, hC, ht⟩ := hopen.exists_lt_isCompact hx
  have : ∀ᶠ y in 𝓝 x, ∀ m ∈ C, y * (m : G) ∈ U := by
    apply hC.eventually_forall_of_forall_eventually
    intro m hm
    have hcont : Continuous (fun z : G × M => z.1 * (z.2 : G)) := by fun_prop
    exact hcont.continuousAt.eventually_mem (hU.mem_nhds (hCU hm))
  filter_upwards [this] with y hy
  simp only [mem_compl_iff, mem_setOf_eq, not_le, transl]
  rw [Measure.map_apply (measurable_transl_fun M y) hU.measurableSet]
  exact ht.trans_le (measure_mono hy)

theorem exists_lift [SecondCountableTopology G] [T2Space G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (P K : Subgroup G) (hP : IsClosed (P : Set G))
    (hK : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) :
    ∃ l : Measure G, l (P : Set G)ᶜ = 0 ∧ (∀ p ∈ P, l.map (fun x => p * x) = l) ∧
      (∀ s : Set G, IsCompact s → l s ≠ ⊤) ∧
      ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ x, ∀ k ∈ K, φ (x * k) = φ x) → ∫⁻ x, φ x ∂l = ∫⁻ x, φ x ∂μ := by
  set M : Subgroup G := P ⊓ K with hM
  have hMc : IsCompact (M : Set G) := hK.inter_left hP
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  let η : Measure M := Measure.haarMeasure (⊤ : PositiveCompacts M)
  haveI : IsProbabilityMeasure η := ⟨by
    have := Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts M))
    simpa using this⟩
  choose s hs r hr hsr using hPK
  let κ : G → Measure G := fun g => transl M η (s g)
  haveI hκp : ∀ g, IsProbabilityMeasure (κ g) := fun g =>
    Measure.isProbabilityMeasure_map (measurable_transl_fun M _).aemeasurable
  have hκ : ∀ p ∈ P, ∀ k ∈ K, κ (p * k) = transl M η p := by
    intro p hp k hk
    have h := hsr (p * k)
    have e : p⁻¹ * s (p * k) = k * (r (p * k))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]; exact h.symm
    have hm : p⁻¹ * s (p * k) ∈ M :=
      ⟨P.mul_mem (P.inv_mem hp) (hs _), by rw [e]; exact K.mul_mem hk (K.inv_mem (hr _))⟩
    rw [← transl_mul_mem M η p hm]
    simp [κ]
  have hmeas : Measurable κ := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    induction A, hA using MeasurableSet.induction_on_open with
    | isOpen U hU =>
      apply measurable_of_Iic
      intro t
      have : (fun g => κ g U) ⁻¹' Iic t = ({x | transl M η x U ≤ t} ∩ (P : Set G)) * (K : Set G) := by
        ext g
        constructor
        · intro hg
          exact ⟨s g, ⟨hg, hs g⟩, r g, hr g, (hsr g).symm⟩
        · rintro ⟨p, ⟨hp1, hp2⟩, k, hk, rfl⟩
          simp only [mem_preimage, mem_Iic]
          rw [hκ p hp2 k hk]
          exact hp1
      rw [this]
      exact (((isClosed_transl_le M η hU t).inter hP).mul_right_of_isCompact hK).measurableSet
    | compl A hA ih =>
      simp only [prob_compl_eq_one_sub hA]
      exact ih.const_sub 1
    | iUnion f hd hf ih =>
      simp only [measure_iUnion hd hf]
      exact Measurable.ennreal_tsum ih
  have happ : ∀ g, ∀ A, MeasurableSet A → κ g A = η ((fun m : M => s g * (m : G)) ⁻¹' A) := fun g A hA =>
    Measure.map_apply (measurable_transl_fun M _) hA
  refine ⟨μ.bind κ, ?_, ?_, ?_, ?_⟩
  · rw [Measure.bind_apply hP.measurableSet.compl hmeas.aemeasurable]
    have : ∀ g, κ g (P : Set G)ᶜ = 0 := by
      intro g
      rw [happ g _ hP.measurableSet.compl]
      convert measure_empty (μ := η)
      ext m
      simpa using P.mul_mem (hs g) m.2.1
    simp [this]
  · intro p hp
    ext A hA
    have hA' : MeasurableSet ((fun x => p * x) ⁻¹' A) := measurable_const_mul p hA
    rw [Measure.map_apply (measurable_const_mul p) hA, Measure.bind_apply hA' hmeas.aemeasurable,
      Measure.bind_apply hA hmeas.aemeasurable, ← lintegral_mul_left_eq_self (fun g => κ g A) p]
    refine lintegral_congr fun g => ?_
    have : κ (p * g) = (κ g).map (fun x => p * x) := by
      conv_lhs => rw [hsr g, ← mul_assoc, hκ _ (P.mul_mem hp (hs g)) _ (hr g), transl_mul]
    rw [this, Measure.map_apply (measurable_const_mul p) hA]
  · intro C hC
    have hCK : IsCompact (C * (K : Set G)) := hC.mul hK
    rw [Measure.bind_apply hC.measurableSet hmeas.aemeasurable]
    refine ne_top_of_le_ne_top (hCK.measure_lt_top (μ := μ)).ne ?_
    rw [← lintegral_indicator_one hCK.measurableSet]
    refine lintegral_mono fun g => ?_
    by_cases hg : g ∈ C * (K : Set G)
    · rw [indicator_of_mem hg]
      exact prob_le_one
    · rw [indicator_of_notMem hg, happ g _ hC.measurableSet]
      refine le_of_eq ?_
      convert measure_empty (μ := η)
      ext m
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      intro hm
      refine hg ⟨_, hm, (m : G)⁻¹ * r g, K.mul_mem (K.inv_mem m.2.2) (hr g), ?_⟩
      simp only
      rw [mul_assoc, mul_inv_cancel_left, ← hsr]
  · intro φ hφ hinv
    rw [Measure.lintegral_bind hmeas.aemeasurable hφ.aemeasurable]
    refine lintegral_congr fun g => ?_
    simp only [κ, transl]
    rw [lintegral_map hφ (measurable_transl_fun M _)]
    have : ∀ m : M, φ (s g * m) = φ g := fun m => by
      rw [hinv _ _ m.2.2]
      conv_rhs => rw [hsr g, hinv _ _ (hr g)]
    simp [this]

theorem exists_eq_smul_subgroup [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    (P : Subgroup G) (hP : IsClosed (P : Set G)) (μ ν : Measure G)
    (hμ1 : μ (P : Set G)ᶜ = 0) (hμ2 : ∀ p ∈ P, μ.map (fun x => p * x) = μ)
    (hμ3 : ∀ s : Set G, IsCompact s → μ s ≠ ⊤) (hμ4 : μ ≠ 0)
    (hν1 : ν (P : Set G)ᶜ = 0) (hν2 : ∀ p ∈ P, ν.map (fun x => p * x) = ν)
    (hν3 : ∀ s : Set G, IsCompact s → ν s ≠ ⊤) (hν4 : ν ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  have hemb : MeasurableEmbedding ((↑) : P → G) := MeasurableEmbedding.subtype_coe hP.measurableSet
  haveI : LocallyCompactSpace P := hP.locallyCompactSpace
  haveI : SecondCountableTopology P := inferInstanceAs (SecondCountableTopology (P : Set G))
  have key : ∀ μ : Measure G, μ (P : Set G)ᶜ = 0 → (∀ p ∈ P, μ.map (fun x => p * x) = μ) →
      (∀ s : Set G, IsCompact s → μ s ≠ ⊤) → μ ≠ 0 →
      ∃ μ' : Measure P, μ'.IsMulLeftInvariant ∧ IsFiniteMeasureOnCompacts μ' ∧ μ' ≠ 0 ∧
        μ = μ'.map (↑) := by
    intro μ h1 h2 h3 h4
    have hmap : μ = (μ.comap ((↑) : P → G)).map (↑) := by
      rw [hemb.map_comap, Subtype.range_coe_subtype]
      exact (Measure.restrict_eq_self_of_ae_mem h1).symm
    refine ⟨μ.comap (↑), ⟨fun p => ?_⟩, ⟨fun C hC => ?_⟩, fun h => h4 (by rw [hmap, h, Measure.map_zero]), hmap⟩
    · ext A hA
      rw [Measure.map_apply (measurable_const_mul p) hA, hemb.comap_apply, hemb.comap_apply]
      conv_rhs => rw [← h2 p p.2]
      rw [Measure.map_apply (measurable_const_mul _) (hemb.measurableSet_image.2 hA)]
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨p * y, hy, rfl⟩
      · rintro ⟨y, hy, hxy⟩
        refine ⟨p⁻¹ * y, by simpa using hy, ?_⟩
        simp only at hxy
        simp [hxy]
    · rw [hemb.comap_apply]
      exact (h3 _ (hC.image continuous_subtype_val)).lt_top
  obtain ⟨μ', a1, a2, a3, a4⟩ := key μ hμ1 hμ2 hμ3 hμ4
  obtain ⟨ν', b1, b2, b3, b4⟩ := key ν hν1 hν2 hν3 hν4
  obtain ⟨c, c0, ct, hc⟩ := exists_eq_smul μ' ν' a3 b3
  exact ⟨c, c0, ct, by rw [a4, b4, hc, Measure.map_smul]⟩

theorem haarProductClosedCompact_holds : Formalism.D.haarProductClosedCompact := by
  intro G _ _ _ _ _ _ _ _ μ _ _ hμ P K hP hK hPK μP μK p1 p2 p3 p4 k1 k2 k3
  haveI : IsProbabilityMeasure μK := ⟨k1⟩
  obtain ⟨l, l1, l2, l3, l4⟩ := exists_lift μ P K hP hK hPK
  have l0 : l ≠ 0 := by
    intro h
    have := l4 (fun _ => 1) measurable_const (fun _ _ _ => rfl)
    rw [h] at this
    simp only [lintegral_zero_measure, lintegral_const, one_mul] at this
    exact hμ (Measure.measure_univ_eq_zero.1 this.symm)
  obtain ⟨c, c0, ct, hc⟩ := exists_eq_smul_subgroup P hP l μP l1 l2 l3 l0 p1 p2 p3 p4
  refine ⟨c, c0, ct, fun Φ hΦ => ?_⟩
  have hΦ2 : Measurable (fun z : G × G => Φ (z.1 * z.2)) := hΦ.comp measurable_mul
  have hφ : Measurable (fun x => ∫⁻ k, Φ (x * k) ∂μK) := hΦ2.lintegral_prod_right'
  have hinv : ∀ x, ∀ k ∈ K, ∫⁻ y, Φ (x * k * y) ∂μK = ∫⁻ y, Φ (x * y) ∂μK := by
    intro x k hk
    conv_rhs => rw [← k3 k hk]
    rw [lintegral_map (f := fun y => Φ (x * y)) (hΦ.comp (measurable_const_mul x)) (measurable_const_mul k)]
    simp [mul_assoc]
  have h1 := l4 _ hφ hinv
  rw [hc, lintegral_smul_measure, smul_eq_mul] at h1
  rw [h1, lintegral_lintegral_swap hΦ2.aemeasurable]
  have : ∀ᵐ k ∂μK, ∫⁻ x, Φ (x * k) ∂μ = ∫⁻ x, Φ x ∂μ := by
    filter_upwards [(mem_ae_iff.2 k2 : (K : Set G) ∈ ae μK)] with k hk
    conv_rhs => rw [← map_mul_right_eq μ hμ K hK hk]
    rw [lintegral_map hΦ (measurable_mul_const k)]
  rw [lintegral_congr_ae this]
  simp

end GlobalTheory.CompanionTheory.HaarPK

end
