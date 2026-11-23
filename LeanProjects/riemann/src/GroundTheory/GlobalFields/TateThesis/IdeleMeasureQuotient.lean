import Mathlib
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureCosets
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.Adele.Discrete

open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise

namespace GroundTheory.Global

noncomputable section

section Discrete

open IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

instance discreteTopology_range_diagonal : DiscreteTopology (diagonal K).range := by
  let f : (diagonal K).range → AdeleRing.principalSubgroup (𝓞 K) K := fun x ↦
    ⟨((x : IdeleGroup K) : 𝔸[K]), by
      obtain ⟨k, hk⟩ := x.2
      exact ⟨(k : K), by rw [← hk]; rfl⟩⟩
  have : DiscreteTopology (AdeleRing.principalSubgroup (𝓞 K) K) :=
    discreteTopology_principalSubgroup K
  exact DiscreteTopology.of_continuous_injective (f := f)
    ((Units.continuous_val.comp continuous_subtype_val).subtype_mk _)
    fun x y h ↦ Subtype.ext (Units.ext (show ((x : IdeleGroup K) : 𝔸[K]) = (y : IdeleGroup K)
      from congrArg Subtype.val h))

abbrev diagonalNormOne : Subgroup (normOneSubgroup K) :=
  (diagonal K).range.subgroupOf (normOneSubgroup K)

instance discreteTopology_diagonalNormOne : DiscreteTopology (diagonalNormOne K) := by
  let f : diagonalNormOne K → (diagonal K).range := fun x ↦
    ⟨((x : normOneSubgroup K) : IdeleGroup K), x.2⟩
  exact DiscreteTopology.of_continuous_injective (f := f)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun x y h ↦ Subtype.ext (Subtype.ext (show ((x : normOneSubgroup K) : IdeleGroup K) =
      ((y : normOneSubgroup K) : IdeleGroup K) from
        congrArg (fun z : (diagonal K).range ↦ (z : IdeleGroup K)) h))

def diagonalToNormOne : Kˣ →* normOneSubgroup K :=
  (diagonal K).codRestrict (normOneSubgroup K) fun k ↦
    range_diagonal_le_normOneSubgroup K ⟨k, rfl⟩

@[simp]
theorem coe_diagonalToNormOne (k : Kˣ) :
    ((diagonalToNormOne K k : normOneSubgroup K) : IdeleGroup K) = diagonal K k :=
  rfl

def diagonalNormOneEquiv : Kˣ ≃ diagonalNormOne K where
  toFun k := ⟨diagonalToNormOne K k, ⟨k, rfl⟩⟩
  invFun x := x.2.choose
  left_inv k := diagonal_injective K ((⟨diagonalToNormOne K k, ⟨k, rfl⟩⟩ :
    diagonalNormOne K).2.choose_spec)
  right_inv x := Subtype.ext (Subtype.ext x.2.choose_spec)

@[simp]
theorem coe_diagonalNormOneEquiv (k : Kˣ) :
    (((diagonalNormOneEquiv K k : diagonalNormOne K) : normOneSubgroup K) : IdeleGroup K) =
      diagonal K k :=
  rfl

instance countable_units : Countable Kˣ := by
  have : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  exact Units.val_injective.countable

instance countable_diagonalNormOne : Countable (diagonalNormOne K) :=
  (diagonalNormOneEquiv K).symm.injective.countable

end Discrete

section FundamentalDomain

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem exists_fundamentalDomain_of_discrete (Γ : Subgroup G) [DiscreteTopology Γ] {D : Set G}
    (hD : IsCompact D) (hcov : ∀ x : G, ∃ γ ∈ Γ, x * γ ∈ D) :
    ∃ E : Set G, MeasurableSet E ∧ IsCompact (closure E) ∧
      ∀ x : G, ∃! γ : Γ.op, γ • x ∈ E := by
  classical

  obtain ⟨U, hUo, hU⟩ : ∃ U : Set G, IsOpen U ∧ Subtype.val ⁻¹' U = ({1} : Set Γ) :=
    isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have h1U : (1 : G) ∈ U := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' U := by rw [hU]; rfl
    exact this
  have hUΓ : ∀ γ ∈ Γ, γ ∈ U → γ = 1 := fun γ hγ hγU ↦ by
    have : (⟨γ, hγ⟩ : Γ) ∈ Subtype.val ⁻¹' U := hγU
    rw [hU] at this
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 this)

  have hW : IsOpen {q : G × G | q.1 / q.2 ∈ U} := hUo.preimage continuous_div'
  obtain ⟨u, v, hu, hv, hu1, hv1, huv⟩ :=
    isOpen_prod_iff.1 hW 1 1 (by simpa using h1U)
  obtain ⟨C, hC, hCn⟩ := exists_compact_mem_nhds (1 : G)
  set V : Set G := u ∩ v ∩ interior C with hVdef
  have hVo : IsOpen V := (hu.inter hv).inter isOpen_interior
  have hV1 : (1 : G) ∈ V := ⟨⟨hu1, hv1⟩, mem_interior_iff_mem_nhds.2 hCn⟩
  have hVdiv : ∀ a ∈ V, ∀ b ∈ V, a / b ∈ U := fun a ha b hb ↦
    huv (Set.mk_mem_prod ha.1.1 hb.1.2)
  have hVC : V ⊆ C := fun a ha ↦ interior_subset ha.2

  obtain ⟨t, ht⟩ := hD.elim_finite_subcover (fun x : G ↦ (x * ·) '' V)
    (fun x ↦ (Homeomorph.mulLeft x).isOpenMap _ hVo)
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, 1, hV1, mul_one x⟩)
  let p : Fin t.card → G := fun i ↦ (t.equivFin.symm i : G)
  let B : Fin t.card → Set G := fun i ↦ (p i * ·) '' V
  let O : Fin t.card → Set G := fun j ↦ ⋃ γ : Γ, (· * (γ : G)) '' B j
  let E : Set G := ⋃ i, (B i \ ⋃ j, ⋃ (_h : j < i), O j)
  have hBo : ∀ i, IsOpen (B i) := fun i ↦ (Homeomorph.mulLeft (p i)).isOpenMap _ hVo
  have hOo : ∀ j, IsOpen (O j) := fun j ↦
    isOpen_iUnion fun γ ↦ (Homeomorph.mulRight (γ : G)).isOpenMap _ (hBo j)
  have hmemO : ∀ j y, y ∈ O j ↔ ∃ γ ∈ Γ, y * γ ∈ B j := by
    intro j y
    simp only [O, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨γ, b, hb, rfl⟩
      exact ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, by rwa [mul_inv_cancel_right]⟩
    · rintro ⟨γ, hγ, hy⟩
      exact ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, y * γ, hy, by simp⟩
  have hDB : D ⊆ ⋃ i, B i := by
    intro y hy
    obtain ⟨z, hz⟩ := Set.mem_iUnion₂.1 (ht hy)
    obtain ⟨hzt, hyz⟩ := hz
    refine Set.mem_iUnion.2 ⟨t.equivFin ⟨z, hzt⟩, ?_⟩
    simp only [B, p, Equiv.symm_apply_apply]
    exact hyz
  refine ⟨E, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun i ↦ (hBo i).measurableSet.diff
      (MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun _ ↦ (hOo j).measurableSet)
  · have hK : IsCompact (⋃ i, (p i * ·) '' C) :=
      isCompact_iUnion fun i ↦ hC.image (continuous_const.mul continuous_id)
    refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
    obtain ⟨a, ha, rfl⟩ := hi.1
    exact Set.mem_iUnion.2 ⟨i, a, hVC ha, rfl⟩
  · intro x
    have hsmul : ∀ γ : Γ.op, γ • x = x * ((γ : Gᵐᵒᵖ).unop) := fun _ ↦ rfl
    have hmemE : ∀ y, y ∈ E ↔ ∃ i, y ∈ B i ∧ ∀ j < i, y ∉ O j := by
      intro y
      simp only [E, Set.mem_iUnion, Set.mem_sdiff, not_exists]

    let S : Finset (Fin t.card) := Finset.univ.filter fun i ↦ ∃ γ ∈ Γ, x * γ ∈ B i
    have hS : S.Nonempty := by
      obtain ⟨γ, hγ, hxγ⟩ := hcov x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hDB hxγ)
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, γ, hγ, hi⟩⟩
    set i := S.min' hS
    obtain ⟨γ, hγ, hγi⟩ := (Finset.mem_filter.1 (S.min'_mem hS)).2
    have hEi : ∀ j < i, x * γ ∉ O j := fun j hj hO ↦ by
      obtain ⟨γ', hγ', hB⟩ := (hmemO j _).1 hO
      have hjS : j ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, γ * γ', Γ.mul_mem hγ hγ',
        by rwa [← mul_assoc]⟩
      exact absurd (S.min'_le j hjS) (not_le.2 hj)
    refine ⟨⟨MulOpposite.op γ, Subgroup.mem_op.2 hγ⟩, ?_, ?_⟩
    · show x * γ ∈ E
      exact (hmemE _).2 ⟨i, hγi, hEi⟩
    · rintro ⟨g, hg⟩ hgE
      have hg' : g.unop ∈ Γ := Subgroup.mem_op.1 hg
      change x * g.unop ∈ E at hgE
      obtain ⟨k, hk, hkO⟩ := (hmemE _).1 hgE
      have hba : g.unop = γ := by
        rcases lt_trichotomy i k with hik | rfl | hki
        · refine absurd ((hmemO i _).2 ⟨g.unop⁻¹ * γ, Γ.mul_mem (Γ.inv_mem hg') hγ, ?_⟩)
            (hkO i hik)
          rwa [mul_assoc, mul_inv_cancel_left]
        · obtain ⟨v₁, hv₁, h₁⟩ := hγi
          obtain ⟨v₂, hv₂, h₂⟩ := hk
          have hdiv : g.unop / γ = v₂ / v₁ := by
            rw [← mul_div_mul_left_eq_div _ _ x, ← h₁, ← h₂, mul_div_mul_left_eq_div]
          have h1 := hUΓ _ (Γ.div_mem hg' hγ) (hdiv ▸ hVdiv v₂ hv₂ v₁ hv₁)
          exact div_eq_one.1 h1
        · refine absurd ((hmemO k _).2 ⟨γ⁻¹ * g.unop, Γ.mul_mem (Γ.inv_mem hγ) hg', ?_⟩)
            (hEi k hki)
          rwa [mul_assoc, mul_inv_cancel_left]
      exact Subtype.ext (MulOpposite.unop_injective hba)

end FundamentalDomain

section NormOneClasses

open IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

theorem exists_fundamentalDomain_normOne :
    ∃ E : Set (normOneSubgroup K), MeasurableSet E ∧ IsCompact (closure E) ∧
      ∀ x : normOneSubgroup K, ∃! γ : (diagonalNormOne K).op, γ • x ∈ E := by
  obtain ⟨D, hD, hDJ, hxD⟩ := exists_isCompact_normOneSubgroup K
  refine exists_fundamentalDomain_of_discrete (diagonalNormOne K)
    (D := Subtype.val ⁻¹' D)
    ((isClosed_normOneSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hD) ?_
  intro x
  obtain ⟨k, hk⟩ := hxD x x.2
  refine ⟨diagonalToNormOne K k, ⟨k, rfl⟩, ?_⟩
  change (x : IdeleGroup K) * diagonal K k ∈ D
  rwa [mul_comm]

def normOneFundamentalDomain : Set (normOneSubgroup K) :=
  (exists_fundamentalDomain_normOne K).choose

theorem measurableSet_normOneFundamentalDomain :
    MeasurableSet (normOneFundamentalDomain K) :=
  (exists_fundamentalDomain_normOne K).choose_spec.1

theorem isCompact_closure_normOneFundamentalDomain :
    IsCompact (closure (normOneFundamentalDomain K)) :=
  (exists_fundamentalDomain_normOne K).choose_spec.2.1

theorem existsUnique_mul_mem_normOneFundamentalDomain (u : normOneSubgroup K) :
    ∃! ξ : Kˣ, u * diagonalToNormOne K ξ ∈ normOneFundamentalDomain K := by
  let e : Kˣ ≃ (diagonalNormOne K).op :=
    (diagonalNormOneEquiv K).trans (diagonalNormOne K).equivOp
  have he : ∀ ξ : Kˣ, e ξ • u = u * diagonalToNormOne K ξ := fun _ ↦ rfl
  obtain ⟨γ, hγ, huniq⟩ := (exists_fundamentalDomain_normOne K).choose_spec.2.2 u
  refine ⟨e.symm γ, ?_, fun ξ hξ ↦ ?_⟩
  · show u * diagonalToNormOne K (e.symm γ) ∈ normOneFundamentalDomain K
    rw [← he, e.apply_symm_apply]
    exact hγ
  · change u * diagonalToNormOne K ξ ∈ normOneFundamentalDomain K at hξ
    rw [← he] at hξ
    rw [← huniq _ hξ, e.symm_apply_apply]

theorem isFundamentalDomain_normOneFundamentalDomain (μ : Measure (normOneSubgroup K)) :
    IsFundamentalDomain (diagonalNormOne K).op (normOneFundamentalDomain K) μ :=
  IsFundamentalDomain.mk' (measurableSet_normOneFundamentalDomain K).nullMeasurableSet
    (exists_fundamentalDomain_normOne K).choose_spec.2.2

theorem normOneMeasure_normOneFundamentalDomain_lt_top :
    normOneMeasure K (normOneFundamentalDomain K) < ∞ :=
  (measure_mono subset_closure).trans_lt
    (isCompact_closure_normOneFundamentalDomain K).measure_lt_top

def normOneClassMeasure : Measure (normOneSubgroup K ⧸ diagonalNormOne K) :=
  Measure.map QuotientGroup.mk ((normOneMeasure K).restrict (normOneFundamentalDomain K))

instance quotientMeasureEqMeasurePreimage_normOneClassMeasure :
    QuotientMeasureEqMeasurePreimage (normOneMeasure K) (normOneClassMeasure K) :=
  (isFundamentalDomain_normOneFundamentalDomain K _).quotientMeasureEqMeasurePreimage_quotientMeasure

instance isFiniteMeasure_normOneClassMeasure : IsFiniteMeasure (normOneClassMeasure K) := by
  have : Fact (normOneMeasure K (normOneFundamentalDomain K) < ∞) :=
    ⟨normOneMeasure_normOneFundamentalDomain_lt_top K⟩
  unfold normOneClassMeasure
  infer_instance

theorem map_restrict_eq_normOneClassMeasure {F : Set (normOneSubgroup K)}
    (hF : IsFundamentalDomain (diagonalNormOne K).op F (normOneMeasure K)) :
    Measure.map QuotientGroup.mk ((normOneMeasure K).restrict F) = normOneClassMeasure K :=
  hF.quotientMeasure_eq _ (isFundamentalDomain_normOneFundamentalDomain K _)

end NormOneClasses

section Unfolding

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

theorem integral_normOneMeasure_eq_setIntegral_tsum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : normOneSubgroup K → E} (hf : Integrable f (normOneMeasure K)) :
    ∫ u, f u ∂normOneMeasure K = ∫ u in normOneFundamentalDomain K,
      ∑' ξ : Kˣ, f (diagonalToNormOne K ξ * u) ∂normOneMeasure K := by
  have h𝓕 := isFundamentalDomain_normOneFundamentalDomain K (normOneMeasure K)
  let e : Kˣ ≃ (diagonalNormOne K).op :=
    (diagonalNormOneEquiv K).trans (diagonalNormOne K).equivOp
  have he : ∀ ξ : Kˣ, ∀ u, f (diagonalToNormOne K ξ * u) = f (e ξ • u) := fun ξ u ↦ by
    change f (diagonalToNormOne K ξ * u) = f (u * diagonalToNormOne K ξ)
    rw [mul_comm]
  calc ∫ u, f u ∂normOneMeasure K
      = ∑' γ : (diagonalNormOne K).op, ∫ u in normOneFundamentalDomain K, f (γ • u)
          ∂normOneMeasure K := h𝓕.integral_eq_tsum'' f hf
    _ = ∫ u in normOneFundamentalDomain K, ∑' γ : (diagonalNormOne K).op, f (γ • u)
          ∂normOneMeasure K := by
        rw [integral_tsum]
        · exact fun γ ↦ (hf.1.comp_quasiMeasurePreserving
            (measurePreserving_smul γ (normOneMeasure K)).quasiMeasurePreserving).restrict
        · rw [← h𝓕.lintegral_eq_tsum'' (‖f ·‖ₑ)]
          exact ne_of_lt hf.2
    _ = ∫ u in normOneFundamentalDomain K, ∑' ξ : Kˣ, f (diagonalToNormOne K ξ * u)
          ∂normOneMeasure K := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
        simp only [he]
        exact (e.tsum_eq (fun γ ↦ f (γ • u))).symm

theorem integral_ideleMeasure_eq_integral_fundamentalDomain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (w : InfinitePlace K) {F : IdeleGroup K → E}
    (hF : Integrable F (ideleMeasure K)) :
    ∫ x, F x ∂ideleMeasure K =
      ∫ t, ∫ u in normOneFundamentalDomain K,
        ∑' ξ : Kˣ, F (diagonal K ξ * moduleSection w t * u) ∂normOneMeasure K
        ∂posRealMeasure := by
  rw [integral_ideleMeasure_eq_integral_normOne w hF]
  have hg : Integrable (fun p : normOneSubgroup K × {r : ℝ // 0 < r} ↦
      F ((p.1 : IdeleGroup K) * moduleSection w p.2))
      ((normOneMeasure K).prod posRealMeasure) := by
    rw [← map_normOneSplitting_eq_prod w]
    refine (integrable_map_equiv (normOneSplitting w).toHomeomorph.toMeasurableEquiv _).2 ?_
    convert hF using 1
    funext x
    exact congrArg F ((normOneSplitting w).symm_apply_apply x)
  refine integral_congr_ae ?_
  filter_upwards [hg.prod_left_ae] with t ht
  rw [integral_normOneMeasure_eq_setIntegral_tsum ht]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only [Subgroup.coe_mul, coe_diagonalToNormOne]
  congr 1
  funext ξ
  rw [mul_right_comm]

end Unfolding

section Volume

variable {K : Type*} [Field K] [NumberField K]

theorem finiteIdeleMeasure_eq_inv_relindex (W : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ)
    (hWo : IsOpen (W : Set (FiniteAdeleRing (𝓞 K) K)ˣ)) (hW : W ≤ finiteIntegralUnits K) :
    finiteIdeleMeasure K W = ((W.relIndex (finiteIntegralUnits K) : ℕ) : ℝ≥0∞)⁻¹ := by
  set H := finiteIntegralUnits K
  have hHm : MeasurableEmbedding (Subtype.val : H → (FiniteAdeleRing (𝓞 K) K)ˣ) :=
    MeasurableEmbedding.subtype_coe (isOpen_finiteIntegralUnits K).measurableSet
  set μ' : Measure H := Measure.comap Subtype.val (finiteIdeleMeasure K)
  have hinv : μ'.IsMulLeftInvariant := by
    refine ⟨fun g ↦ Measure.ext fun s hs ↦ ?_⟩
    rw [Measure.map_apply (measurable_const_mul g) hs, hHm.comap_apply, hHm.comap_apply]
    have : Subtype.val '' ((fun x : H ↦ g * x) ⁻¹' s) =
        (fun x ↦ (g : (FiniteAdeleRing (𝓞 K) K)ˣ) * x) ⁻¹' (Subtype.val '' s) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        refine ⟨g⁻¹ * y, by simpa using hy, ?_⟩
        simp [hyx]
    rw [this, measure_preimage_mul]
  have hc : CompactSpace H := isCompact_iff_compactSpace.1 (isCompact_finiteIntegralUnits K)
  have hWHo : IsOpen ((W.subgroupOf H : Subgroup H) : Set H) :=
    hWo.preimage continuous_subtype_val
  have : Finite (H ⧸ W.subgroupOf H) := Subgroup.quotient_finite_of_isOpen _ hWHo
  have : (W.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h := Subgroup.index_mul_measure (W.subgroupOf H) hWHo.measurableSet μ'
  have h1 : μ' Set.univ = 1 := by
    rw [hHm.comap_apply, Set.image_univ, Subtype.range_coe]
    exact finiteIdeleMeasure_finiteIntegralUnits K
  have h2 : μ' (W.subgroupOf H : Set H) = finiteIdeleMeasure K W := by
    rw [hHm.comap_apply]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hW hx⟩, hx, rfl⟩
  rw [h1, h2] at h
  rw [Subgroup.relIndex]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at h)

end Volume

end

end GroundTheory.Global
