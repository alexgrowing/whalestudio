import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RightCosetSpaceCompact

open MeasureTheory Topology Filter Set TopologicalSpace
open scoped ENNReal Pointwise Uniformity

namespace GroundTheory.Automorphic

noncomputable section

theorem polishSpace_of_locallyCompact {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] :
    PolishSpace G := by
  let _ := IsTopologicalGroup.rightUniformSpace G
  have : IsRightUniformGroup G := ⟨rfl⟩
  have : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace
  have : (𝓤 G).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_one']
    infer_instance
  exact {}

variable {G : Type*} [Group G]

abbrev RightCosetSpace (Γ : Subgroup G) : Type _ := Quotient (MulAction.orbitRel Γ G)

namespace RightCosetSpace

variable (Γ : Subgroup G)

def mk : G → RightCosetSpace Γ := Quotient.mk _

variable {Γ}

theorem mk_eq_mk_iff {g h : G} : mk Γ g = mk Γ h ↔ ∃ γ : Γ, γ • h = g :=
  Quotient.eq.trans MulAction.orbitRel_apply

@[simp]
theorem mk_smul (γ : Γ) (g : G) : mk Γ (γ • g) = mk Γ g :=
  mk_eq_mk_iff.2 ⟨γ, rfl⟩

theorem mk_mul_of_mem {γ : G} (hγ : γ ∈ Γ) (g : G) : mk Γ (γ * g) = mk Γ g :=
  mk_smul ⟨γ, hγ⟩ g

variable (Γ)

theorem mk_surjective : Function.Surjective (mk Γ) :=
  Quotient.mk_surjective

def rightMul (g : G) : RightCosetSpace Γ → RightCosetSpace Γ :=
  Quotient.map' (· * g) fun a b h ↦ by
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.1 h
    refine MulAction.orbitRel_apply.2 ⟨γ, ?_⟩
    change (γ : G) * (b * g) = a * g
    rw [← mul_assoc]
    exact congrArg (· * g) hγ

variable {Γ}

@[simp]
theorem rightMul_mk (g x : G) : rightMul Γ g (mk Γ x) = mk Γ (x * g) :=
  rfl

variable (Γ)

@[simp]
theorem rightMul_one : rightMul Γ 1 = id := by
  funext x
  obtain ⟨x, rfl⟩ := mk_surjective Γ x
  simp

theorem rightMul_mul (g h : G) : rightMul Γ (g * h) = rightMul Γ h ∘ rightMul Γ g := by
  funext x
  obtain ⟨x, rfl⟩ := mk_surjective Γ x
  simp [mul_assoc]

theorem rightMul_rightMul (g h : G) (x : RightCosetSpace Γ) :
    rightMul Γ h (rightMul Γ g x) = rightMul Γ (g * h) x := by
  rw [rightMul_mul]
  rfl

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem continuous_mk : Continuous (mk Γ) :=
  continuous_quotient_mk'

theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk Γ) :=
  MulAction.isOpenQuotientMap_quotientMk

theorem isOpenMap_mk : IsOpenMap (mk Γ) :=
  (isOpenQuotientMap_mk Γ).isOpenMap

theorem continuous_rightMul_prod :
    Continuous fun p : RightCosetSpace Γ × G ↦ rightMul Γ p.2 p.1 := by
  have hq : IsQuotientMap (Prod.map (mk Γ) (id : G → G)) :=
    ((isOpenQuotientMap_mk Γ).prodMap IsOpenQuotientMap.id).isQuotientMap
  rw [hq.continuous_iff]
  exact (continuous_mk Γ).comp (continuous_fst.mul continuous_snd)

theorem continuous_rightMul (g : G) : Continuous (rightMul Γ g) :=
  (continuous_rightMul_prod Γ).comp (continuous_id.prodMk continuous_const)

def rightMulHomeomorph (g : G) : RightCosetSpace Γ ≃ₜ RightCosetSpace Γ where
  toFun := rightMul Γ g
  invFun := rightMul Γ g⁻¹
  left_inv x := by rw [← Function.comp_apply (f := rightMul Γ g⁻¹), ← rightMul_mul]; simp
  right_inv x := by rw [← Function.comp_apply (f := rightMul Γ g), ← rightMul_mul]; simp
  continuous_toFun := continuous_rightMul Γ g
  continuous_invFun := continuous_rightMul Γ g⁻¹

instance [LocallyCompactSpace G] : LocallyCompactSpace (RightCosetSpace Γ) :=
  (isOpenQuotientMap_mk Γ).locallyCompactSpace

instance [SecondCountableTopology G] : SecondCountableTopology (RightCosetSpace Γ) :=
  ContinuousConstSMul.secondCountableTopology

theorem exists_isCompact_subset_mk_image [LocallyCompactSpace G] {K : Set (RightCosetSpace Γ)}
    (hK : IsCompact K) : ∃ D : Set G, IsCompact D ∧ K ⊆ mk Γ '' D :=
  by apply _root_.UpperTheory.Reformulated.B.RightCosetSpaceCompact.exists_isCompact_subset_mk_image <;> assumption

section Discrete

variable [DiscreteTopology Γ]

section T2

variable [T2Space G]

instance properlyDiscontinuousSMul : ProperlyDiscontinuousSMul Γ G :=
  Γ.properlyDiscontinuousSMul_of_tendsto_cofinite
    (Γ.tendsto_coe_cofinite_of_discrete (isDiscrete_iff_discreteTopology.2 ‹_›))

theorem t2Space [LocallyCompactSpace G] : T2Space (RightCosetSpace Γ) := inferInstance

instance countable_of_discrete [SecondCountableTopology G] : Countable Γ :=
  separableSpace_iff_countable.1 inferInstance

end T2

theorem exists_isOpen_one_mem_injOn {C : Set G} (hC : C ∈ 𝓝 (1 : G)) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ V ⊆ C ∧
      ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ Γ → a = b := by
  obtain ⟨U, hUo, hU⟩ : ∃ U : Set G, IsOpen U ∧ Subtype.val ⁻¹' U = ({1} : Set Γ) :=
    isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have h1U : (1 : G) ∈ U := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' U := by rw [hU]; rfl
    exact this
  have hUΓ : ∀ γ ∈ Γ, γ ∈ U → γ = 1 := fun γ hγ hγU ↦ by
    have : (⟨γ, hγ⟩ : Γ) ∈ Subtype.val ⁻¹' U := hγU
    rw [hU] at this
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 this)
  have hW : IsOpen {q : G × G | q.1 * q.2⁻¹ ∈ U} :=
    hUo.preimage (continuous_fst.mul continuous_snd.inv)
  obtain ⟨u, v, hu, hv, hu1, hv1, huv⟩ := isOpen_prod_iff.1 hW 1 1 (by simpa using h1U)
  refine ⟨u ∩ v ∩ interior C, (hu.inter hv).inter isOpen_interior,
    ⟨⟨hu1, hv1⟩, mem_interior_iff_mem_nhds.2 hC⟩, fun a ha ↦ interior_subset ha.2, ?_⟩
  intro a ha b hb hab
  have := hUΓ _ hab (huv (Set.mk_mem_prod ha.1.1 hb.1.2))
  exact mul_inv_eq_one.1 this

end Discrete

section FundamentalDomain

variable {Γ} [MeasurableSpace G] [BorelSpace G]

theorem exists_fundamentalDomain_of_cover {V : Set G} (hVo : IsOpen V)
    (hV : ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ Γ → a = b) (p : ℕ → G)
    (hcov : ∀ x : G, ∃ γ : Γ, ∃ i, γ • x ∈ (· * p i) '' V) :
    ∃ E : Set G, MeasurableSet E ∧ E ⊆ ⋃ i, (· * p i) '' V ∧
      ∀ x : G, ∃! γ : Γ, γ • x ∈ E := by
  classical
  set B : ℕ → Set G := fun i ↦ (· * p i) '' V with hBdef
  set O : ℕ → Set G := fun j ↦ ⋃ γ : Γ, (fun y : G ↦ γ • y) ⁻¹' B j with hOdef
  set E : Set G := ⋃ i, (B i \ ⋃ j, ⋃ (_ : j < i), O j) with hEdef
  have hBo : ∀ i, IsOpen (B i) := fun i ↦ isOpenMap_mul_right (p i) _ hVo
  have hOo : ∀ j, IsOpen (O j) := fun j ↦
    isOpen_iUnion fun γ ↦ (hBo j).preimage (continuous_const_smul γ)
  have hmemO : ∀ j y, y ∈ O j ↔ ∃ γ : Γ, γ • y ∈ B j := by
    intro j y
    simp only [hOdef, Set.mem_iUnion, Set.mem_preimage]
  have hmemE : ∀ y, y ∈ E ↔ ∃ i, y ∈ B i ∧ ∀ j < i, y ∉ O j := by
    intro y
    simp only [hEdef, Set.mem_iUnion, Set.mem_sdiff, not_exists]
  refine ⟨E, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun i ↦ (hBo i).measurableSet.diff
      (MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun _ ↦ (hOo j).measurableSet)
  · intro y hy
    obtain ⟨i, hi, -⟩ := (hmemE y).1 hy
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  · intro x
    have hS : ∃ i, ∃ γ : Γ, γ • x ∈ B i := by
      obtain ⟨γ, i, hi⟩ := hcov x
      exact ⟨i, γ, hi⟩
    set i := Nat.find hS
    obtain ⟨γ, hγi⟩ := Nat.find_spec hS
    have hEi : ∀ j < i, γ • x ∉ O j := fun j hj hO ↦ by
      obtain ⟨γ', hB⟩ := (hmemO j _).1 hO
      exact Nat.find_min hS hj ⟨γ' * γ, by rwa [mul_smul]⟩
    refine ⟨γ, (hmemE _).2 ⟨i, hγi, hEi⟩, ?_⟩
    intro δ hδ
    obtain ⟨k, hk, hkO⟩ := (hmemE _).1 hδ
    rcases lt_trichotomy i k with hik | rfl | hki
    · refine absurd ((hmemO i _).2 ⟨γ * δ⁻¹, ?_⟩) (hkO i hik)
      rwa [mul_smul, inv_smul_smul]
    · obtain ⟨v₁, hv₁, h₁⟩ := hγi
      obtain ⟨v₂, hv₂, h₂⟩ := hk
      have hmem : v₂ * v₁⁻¹ ∈ Γ := by
        have : v₂ * v₁⁻¹ = ((δ * γ⁻¹ : Γ) : G) := by
          have h₁' : v₁ = (γ : G) * x * (p i)⁻¹ := by
            rw [eq_mul_inv_iff_mul_eq]; exact h₁
          have h₂' : v₂ = (δ : G) * x * (p i)⁻¹ := by
            rw [eq_mul_inv_iff_mul_eq]; exact h₂
          rw [h₁', h₂']
          simp [mul_assoc]
        rw [this]
        exact (δ * γ⁻¹).2
      have hv : v₂ = v₁ := hV v₂ hv₂ v₁ hv₁ hmem
      have : (δ : G) * x = (γ : G) * x := by
        change δ • x = γ • x
        rw [← h₁, ← h₂, hv]
      exact Subtype.ext (mul_right_cancel this)
    · exact absurd hki (not_lt.2 (Nat.find_min' hS ⟨δ, hk⟩))

variable (Γ) [DiscreteTopology Γ]

theorem exists_fundamentalDomain [SecondCountableTopology G] :
    ∃ E : Set G, MeasurableSet E ∧ ∀ x : G, ∃! γ : Γ, γ • x ∈ E := by
  obtain ⟨V, hVo, hV1, -, hV⟩ := exists_isOpen_one_mem_injOn Γ (univ_mem (f := 𝓝 (1 : G)))
  obtain ⟨r, hr, hcov⟩ := isLindelof_univ.elim_countable_subcover (fun x : G ↦ (· * x) '' V)
    (fun x ↦ isOpenMap_mul_right x _ hVo)
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, 1, hV1, one_mul x⟩)
  have hrne : r.Nonempty := by
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 (hcov (Set.mem_univ (1 : G)))
    exact ⟨x, hx⟩
  obtain ⟨p, rfl⟩ := hr.exists_eq_range hrne
  obtain ⟨E, hE, -, hEu⟩ := exists_fundamentalDomain_of_cover hVo hV p fun x ↦ by
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov (Set.mem_univ x))
    obtain ⟨i, rfl⟩ := hy
    exact ⟨1, i, by simpa using hxy⟩
  exact ⟨E, hE, hEu⟩

end FundamentalDomain

section Measure

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [DiscreteTopology Γ]

def fundamentalDomain : Set G :=
  (exists_fundamentalDomain Γ).choose

theorem measurableSet_fundamentalDomain : MeasurableSet (fundamentalDomain Γ) :=
  (exists_fundamentalDomain Γ).choose_spec.1

theorem existsUnique_smul_mem_fundamentalDomain (x : G) :
    ∃! γ : Γ, γ • x ∈ fundamentalDomain Γ :=
  (exists_fundamentalDomain Γ).choose_spec.2 x

theorem isFundamentalDomain_fundamentalDomain (μ : Measure G) :
    IsFundamentalDomain Γ (fundamentalDomain Γ) μ :=
  IsFundamentalDomain.mk' (measurableSet_fundamentalDomain Γ).nullMeasurableSet
    (existsUnique_smul_mem_fundamentalDomain Γ)

def quotientMeasure (μ : Measure G) : Measure (RightCosetSpace Γ) :=
  Measure.map (mk Γ) (μ.restrict (fundamentalDomain Γ))

theorem injOn_mk_fundamentalDomain : Set.InjOn (mk Γ) (fundamentalDomain Γ) := by
  intro x hx y hy hxy
  obtain ⟨γ, rfl⟩ := mk_eq_mk_iff.1 hxy
  obtain ⟨δ, -, hδ⟩ := existsUnique_smul_mem_fundamentalDomain Γ y
  have h1 := hδ γ hx
  have h2 := hδ 1 (by simpa using hy)
  rw [h1, ← h2, one_smul]

theorem mk_image_fundamentalDomain : mk Γ '' fundamentalDomain Γ = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨x, rfl⟩ := mk_surjective Γ x
  obtain ⟨γ, hγ, -⟩ := existsUnique_smul_mem_fundamentalDomain Γ x
  exact ⟨γ • x, hγ, mk_smul γ x⟩

variable [LocallyCompactSpace G] [T2Space G]

instance borelSpace : BorelSpace (RightCosetSpace Γ) := by
  have := polishSpace_of_locallyCompact (G := G)
  exact Quotient.borelSpace

theorem measurable_mk : Measurable (mk Γ) :=
  (continuous_mk Γ).measurable

def fundamentalDomainEquiv : fundamentalDomain Γ ≃ᵐ RightCosetSpace Γ where
  toEquiv := Equiv.ofBijective (fun x ↦ mk Γ x)
    ⟨fun x y h ↦ Subtype.ext (injOn_mk_fundamentalDomain Γ x.2 y.2 h), fun x ↦ by
      obtain ⟨y, hy, rfl⟩ := (mk_image_fundamentalDomain Γ).symm ▸ Set.mem_univ x
      exact ⟨⟨y, hy⟩, rfl⟩⟩
  measurable_toFun := (measurable_mk Γ).comp measurable_subtype_coe
  measurable_invFun := by
    intro A hA
    set e := Equiv.ofBijective (fun x : fundamentalDomain Γ ↦ mk Γ x)
      ⟨fun x y h ↦ Subtype.ext (injOn_mk_fundamentalDomain Γ x.2 y.2 h), fun x ↦ by
        obtain ⟨y, hy, rfl⟩ := (mk_image_fundamentalDomain Γ).symm ▸ Set.mem_univ x
        exact ⟨⟨y, hy⟩, rfl⟩⟩
    have himage : e.symm ⁻¹' A = mk Γ '' (Subtype.val '' A) := by
      rw [← Equiv.image_eq_preimage_symm, ← Set.image_comp]
      rfl
    have hS : MeasurableSet (Subtype.val '' A : Set G) :=
      (measurableSet_fundamentalDomain Γ).subtype_image hA
    change MeasurableSet (e.symm ⁻¹' A)
    rw [himage, measurableSet_quotient]
    change MeasurableSet (mk Γ ⁻¹' (mk Γ '' (Subtype.val '' A)))
    have : mk Γ ⁻¹' (mk Γ '' (Subtype.val '' A)) = ⋃ γ : Γ, (γ • ·) '' (Subtype.val '' A) :=
      MulAction.quotient_preimage_image_eq_union_mul _
    rw [this]
    refine MeasurableSet.iUnion fun γ ↦ ?_
    rw [Set.image_smul]
    exact hS.const_smul γ

@[simp]
theorem fundamentalDomainEquiv_apply (x : fundamentalDomain Γ) :
    fundamentalDomainEquiv Γ x = mk Γ x :=
  rfl

variable (μ : Measure G)

theorem quotientMeasure_eq_map_fundamentalDomainEquiv :
    quotientMeasure Γ μ = Measure.map (fundamentalDomainEquiv Γ) (μ.comap Subtype.val) := by
  rw [quotientMeasure, ← map_comap_subtype_coe (measurableSet_fundamentalDomain Γ),
    Measure.map_map (measurable_mk Γ) measurable_subtype_coe]
  rfl

theorem integral_quotientMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : RightCosetSpace Γ → E) :
    ∫ x, h x ∂quotientMeasure Γ μ = ∫ g in fundamentalDomain Γ, h (mk Γ g) ∂μ := by
  rw [quotientMeasure_eq_map_fundamentalDomainEquiv, integral_map_equiv,
    ← integral_subtype_comap (measurableSet_fundamentalDomain Γ)]
  rfl

theorem lintegral_quotientMeasure (h : RightCosetSpace Γ → ℝ≥0∞) :
    ∫⁻ x, h x ∂quotientMeasure Γ μ = ∫⁻ g in fundamentalDomain Γ, h (mk Γ g) ∂μ := by
  rw [quotientMeasure_eq_map_fundamentalDomainEquiv, lintegral_map_equiv,
    ← lintegral_subtype_comap (measurableSet_fundamentalDomain Γ)]
  rfl

variable {Γ} [μ.IsMulLeftInvariant]

omit [LocallyCompactSpace G] [T2Space G] in

theorem map_restrict_eq_quotientMeasure {F : Set G} (hF : IsFundamentalDomain Γ F μ) :
    Measure.map (mk Γ) (μ.restrict F) = quotientMeasure Γ μ :=
  hF.quotientMeasure_eq μ (isFundamentalDomain_fundamentalDomain Γ μ)

instance quotientMeasureEqMeasurePreimage :
    QuotientMeasureEqMeasurePreimage μ (quotientMeasure Γ μ) :=
  (isFundamentalDomain_fundamentalDomain Γ μ).quotientMeasureEqMeasurePreimage_quotientMeasure

theorem quotientMeasure_apply {F : Set G} (hF : IsFundamentalDomain Γ F μ)
    {A : Set (RightCosetSpace Γ)} (hA : MeasurableSet A) :
    quotientMeasure Γ μ A = μ (mk Γ ⁻¹' A ∩ F) := by
  rw [← map_restrict_eq_quotientMeasure μ hF, Measure.map_apply (measurable_mk Γ) hA,
    Measure.restrict_apply (measurable_mk Γ hA)]

theorem quotientMeasure_univ {F : Set G} (hF : IsFundamentalDomain Γ F μ) :
    quotientMeasure Γ μ univ = μ F := by
  rw [quotientMeasure_apply μ hF MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]

theorem quotientMeasure_mk_image_le {D : Set G} (hD : MeasurableSet (mk Γ '' D)) :
    quotientMeasure Γ μ (mk Γ '' D) ≤ μ D := by
  have hF := isFundamentalDomain_fundamentalDomain Γ μ
  rw [quotientMeasure_apply μ hF hD]
  have : mk Γ ⁻¹' (mk Γ '' D) = ⋃ γ : Γ, (γ • ·) '' D :=
    MulAction.quotient_preimage_image_eq_union_mul _
  rw [this, Set.iUnion_inter, hF.measure_eq_tsum D]
  refine (measure_iUnion_le _).trans (le_of_eq ?_)
  simp only [Set.image_smul]

instance isFiniteMeasureOnCompacts [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (quotientMeasure Γ μ) := by
  refine ⟨fun K hK ↦ ?_⟩
  obtain ⟨D, hD, hKD⟩ := exists_isCompact_subset_mk_image Γ hK
  have hm : MeasurableSet (mk Γ '' D) := (hD.image (continuous_mk Γ)).isClosed.measurableSet
  exact (measure_mono hKD).trans_lt
    ((quotientMeasure_mk_image_le μ hm).trans_lt hD.measure_lt_top)

instance isFiniteMeasure [IsFiniteMeasureOnCompacts μ] [CompactSpace (RightCosetSpace Γ)] :
    IsFiniteMeasure (quotientMeasure Γ μ) :=
  ⟨isCompact_univ.measure_lt_top⟩

instance regular [IsFiniteMeasureOnCompacts μ] : (quotientMeasure Γ μ).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

instance isOpenPosMeasure [μ.IsOpenPosMeasure] : (quotientMeasure Γ μ).IsOpenPosMeasure := by
  refine ⟨fun U hUo hUne hU0 ↦ ?_⟩
  have hF := isFundamentalDomain_fundamentalDomain Γ μ
  have hV : IsOpen (mk Γ ⁻¹' U) := hUo.preimage (continuous_mk Γ)
  have hVne : (mk Γ ⁻¹' U).Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨y, rfl⟩ := mk_surjective Γ x
    exact ⟨y, hx⟩
  refine hV.measure_ne_zero μ hVne ?_
  have hinv : ∀ γ : Γ, γ • (mk Γ ⁻¹' U) = mk Γ ⁻¹' U := fun γ ↦ by
    ext y
    simp [Set.mem_smul_set_iff_inv_smul_mem]
  rw [hF.measure_eq_tsum (mk Γ ⁻¹' U)]
  simp only [hinv]
  rw [quotientMeasure_apply μ hF hUo.measurableSet] at hU0
  simp [hU0]

theorem map_rightMul_quotientMeasure [μ.IsMulRightInvariant] (g : G) :
    Measure.map (rightMul Γ g) (quotientMeasure Γ μ) = quotientMeasure Γ μ := by
  set F := fundamentalDomain Γ
  have hF' : IsFundamentalDomain Γ ((· * g⁻¹) ⁻¹' F) μ :=
    (isFundamentalDomain_fundamentalDomain Γ μ).preimage_of_equiv
      (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving (e := id) Function.bijective_id
      fun γ x ↦ mul_assoc (γ : G) x g⁻¹
  have hmg : Measurable (· * g : G → G) := measurable_mul_const g
  have h1 : (· * g : G → G) ⁻¹' ((· * g⁻¹) ⁻¹' F) = F := by
    ext x
    simp
  have hcomm : rightMul Γ g ∘ mk Γ = mk Γ ∘ (· * g) := rfl
  have key : Measure.map (mk Γ) (μ.restrict ((· * g⁻¹) ⁻¹' F)) = quotientMeasure Γ μ :=
    map_restrict_eq_quotientMeasure μ hF'
  conv_rhs => rw [← key]
  have h2 : Measure.map (· * g) (μ.restrict F) = μ.restrict ((· * g⁻¹) ⁻¹' F) := by
    conv_lhs => rw [← h1]
    rw [← Measure.restrict_map hmg ((measurableSet_fundamentalDomain Γ).preimage
      (measurable_mul_const g⁻¹)), map_mul_right_eq_self]
  rw [show quotientMeasure Γ μ = Measure.map (mk Γ) (μ.restrict F) from rfl,
    Measure.map_map (continuous_rightMul Γ g).measurable (measurable_mk Γ), hcomm,
    ← Measure.map_map (measurable_mk Γ) hmg, h2]

theorem measurePreserving_rightMul [μ.IsMulRightInvariant] (g : G) :
    MeasurePreserving (rightMul Γ g) (quotientMeasure Γ μ) (quotientMeasure Γ μ) :=
  ⟨(continuous_rightMul Γ g).measurable, map_rightMul_quotientMeasure μ g⟩

theorem lintegral_eq_lintegral_automorphize {f : G → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ g, f g ∂μ = ∫⁻ x, MulAction.automorphize f x ∂quotientMeasure Γ μ := by
  have hF := isFundamentalDomain_fundamentalDomain Γ μ
  rw [lintegral_quotientMeasure, hF.lintegral_eq_tsum'' f, ← lintegral_tsum]
  · rfl
  · exact fun γ ↦ (hf.comp_quasiMeasurePreserving
      (measurePreserving_smul γ μ).quasiMeasurePreserving).restrict

theorem integral_eq_integral_automorphize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : G → E} (hf : Integrable f μ) :
    ∫ g, f g ∂μ = ∫ x, MulAction.automorphize f x ∂quotientMeasure Γ μ := by
  have hF := isFundamentalDomain_fundamentalDomain Γ μ
  rw [integral_quotientMeasure]
  calc ∫ g, f g ∂μ = ∑' γ : Γ, ∫ g in fundamentalDomain Γ, f (γ • g) ∂μ :=
        hF.integral_eq_tsum'' f hf
    _ = ∫ g in fundamentalDomain Γ, ∑' γ : Γ, f (γ • g) ∂μ := by
        rw [integral_tsum]
        · exact fun γ ↦ (hf.1.comp_quasiMeasurePreserving
            (measurePreserving_smul γ μ).quasiMeasurePreserving).restrict
        · rw [← hF.lintegral_eq_tsum'' (‖f ·‖ₑ)]
          exact hf.2.ne
    _ = ∫ g in fundamentalDomain Γ, MulAction.automorphize f (mk Γ g) ∂μ := rfl

theorem integral_mul_eq_integral_mul_automorphize {𝕜 : Type*} [RCLike 𝕜] {f : G → 𝕜}
    {φ : RightCosetSpace Γ → 𝕜} (h : Integrable (fun g ↦ φ (mk Γ g) * f g) μ) :
    ∫ g, φ (mk Γ g) * f g ∂μ = ∫ x, φ x * MulAction.automorphize f x ∂quotientMeasure Γ μ := by
  rw [integral_eq_integral_automorphize (Γ := Γ) μ h]
  have H := MulAction.automorphize_smul_left (α := Γ) f φ
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  exact congrFun H x

end Measure

end Topology

end RightCosetSpace

end

end GroundTheory.Automorphic
