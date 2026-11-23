import Mathlib
import GroundTheory.LocalFields.LocalArtinUniqueness
import GroundTheory.LocalFields.LocalReciprocityLimitAbstract

noncomputable section

namespace GroundTheory.LocalField

open Abstract ValuativeRel

section Galois

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (E : IntermediateField K Ω)

def restrictScalarsHom : (Ω ≃ₐ[E] Ω) →* (Ω ≃ₐ[K] Ω) :=
  (E.fixingSubgroup.subtype).comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom

@[simp]
theorem restrictScalarsHom_apply (σ : Ω ≃ₐ[E] Ω) (x : Ω) : restrictScalarsHom E σ x = σ x :=
  rfl

variable [FiniteDimensional K E]

theorem continuous_restrictScalarsHom : Continuous (restrictScalarsHom (K := K) (Ω := Ω) E) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨M, hM, hMs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
  have : FiniteDimensional K (M ⊔ E : IntermediateField K Ω) := inferInstance
  have : FiniteDimensional E (IntermediateField.extendScalars (le_sup_right : E ≤ M ⊔ E)) :=
    finiteDimensional_extendScalars _
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.extendScalars (le_sup_right : E ≤ M ⊔ E), inferInstance, fun σ hσ => ?_⟩
  apply hMs
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x
    ((IntermediateField.mem_extendScalars _).2 (le_sup_left (a := M) (b := E) hx))

variable [IsGalois K Ω]

def fixingSubgroupHomeomorph :
    ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ≃ₜ* (Ω ≃ₐ[E] Ω) :=
  have : T2Space (Ω ≃ₐ[K] Ω) := krullTopology_t2
  let e := (IntermediateField.fixingSubgroupEquiv E).symm.trans
    (MulEquiv.subgroupCongr (coe_fixingOpenSubgroup E).symm)
  have hc : Continuous e :=
    Continuous.subtype_mk (continuous_restrictScalarsHom E) fun σ => (e σ).2
  ContinuousMulEquiv.symm
    { e with
      continuous_toFun := hc
      continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

@[simp]
theorem fixingSubgroupHomeomorph_apply
    (σ : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) (x : Ω) :
    fixingSubgroupHomeomorph E σ x = (σ : Ω ≃ₐ[K] Ω) x :=
  rfl

omit [IsGalois K Ω] in

theorem maximalAbelianExtension_le_restrictScalars :
    maximalAbelianExtension K Ω ≤ (maximalAbelianExtension E Ω).restrictScalars K := by
  intro y hy
  rw [IntermediateField.mem_restrictScalars]
  change y ∈ IntermediateField.fixedField _
  rw [IntermediateField.mem_fixedField_iff]
  intro g hg
  have hle : (commutator (Ω ≃ₐ[E] Ω)).topologicalClosure ≤
      (commutator (Ω ≃ₐ[K] Ω)).topologicalClosure.comap (restrictScalarsHom E) := by
    refine Subgroup.topologicalClosure_minimal _ ?_
      ((Subgroup.isClosed_topologicalClosure _).preimage (continuous_restrictScalarsHom E))
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.le_topologicalClosure _
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  exact (IntermediateField.mem_fixedField_iff _ _).1 hy _ (hle hg)

end Galois

section Data

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]

instance isSepClosure_intermediateField (E : IntermediateField K Ω) : IsSepClosure E Ω :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K E Ω⟩

variable (E : IntermediateField K Ω) [FiniteDimensional K E]

variable (K) in

def unitsEquivFixingOpen :
    fixedModule Ωˣ ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ≃* Eˣ :=
  unitsEquivOfForall _ E
    (mem_iff_forall_of_fixingSubgroup_eq ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) :
      Subgroup (Ω ≃ₐ[K] Ω)) rfl)

theorem relDeg_fixingOpenSubgroup
    (σ : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    (localClassFieldData K Ω).relDeg (fixingOpenSubgroup E) σ =
      unramifiedDegree E Ω (fixingSubgroupHomeomorph E σ) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hi : inertiaDegree (unramifiedDegree K Ω)
      ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) = residueDegree K E :=
    inertiaDegree_unramifiedDegree_fixingSubgroup E
  rw [ClassFieldData.relDeg_eq_iff, localClassFieldData_deg, hi]
  exact unramifiedDegree_fixingSubgroup E σ

theorem valuation_fixingOpenSubgroup
    (a : fixedModule Ωˣ ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    (localClassFieldData K Ω).valuation (fixingOpenSubgroup E) a =
      Multiplicative.ofAdd ((ord ((unitsEquivFixingOpen K E a : Eˣ) : E) : ℤ) : ℤ̂) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hf : residueDegree K E ≠ 0 := (residueDegree_pos K E).ne'
  have h := (localClassFieldData K Ω).valuation_pow (fixingOpenSubgroup E) a
  have hi : inertiaDegree (unramifiedDegree K Ω)
      ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) = residueDegree K E :=
    inertiaDegree_unramifiedDegree_fixingSubgroup E
  rw [localClassFieldData_deg, hi, localClassFieldData_val, localValuation_apply] at h
  have : (E.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  erw [baseUnitsEquiv_norm E a] at h
  rw [← Abstract.ProfiniteInteger.pow_left_inj hf, h]
  apply Multiplicative.toAdd.injective
  rw [toAdd_ordUnitsHom, coe_normUnits, ord_norm, toAdd_pow, toAdd_ofAdd, Int.cast_mul,
    Int.cast_natCast, nsmul_eq_mul]
  rfl

end Data

section Limit

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]

attribute [local instance] isDiscreteModule_units

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  [FiniteDimensional K E] in
theorem le_restrictScalars (L : IntermediateField E Ω) : E ≤ L.restrictScalars K := fun x hx => by
  rw [IntermediateField.mem_restrictScalars]
  exact L.algebraMap_mem ⟨x, hx⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  [FiniteDimensional K E] in
theorem extendScalars_restrictScalars' (L : IntermediateField E Ω) :
    IntermediateField.extendScalars (le_restrictScalars E L) = L := by
  ext x
  rw [IntermediateField.mem_extendScalars, IntermediateField.mem_restrictScalars]

variable (K) in

def baseChangeArtinMap : Eˣ →* (maximalAbelianExtension E Ω ≃ₐ[E] maximalAbelianExtension E Ω) :=
  (topologicalAbelianizationEquiv E Ω).toMulEquiv.toMonoidHom.comp
    ((topologicalAbelianizationMap (fixingSubgroupHomeomorph E).toMulEquiv.toMonoidHom
      (fixingSubgroupHomeomorph E).continuous).comp
      (((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E)).comp
        (unitsEquivFixingOpen K E).symm.toMonoidHom))

omit [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem baseChangeArtinMap_apply (x : Eˣ)
    (g : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)))
    (hg : (QuotientGroup.mk g : TopologicalAbelianization _) =
      (localClassFieldData K Ω).reciprocityLimit
      (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) ((unitsEquivFixingOpen K E).symm x))
    (y : maximalAbelianExtension E Ω) :
    ((baseChangeArtinMap K E x y : maximalAbelianExtension E Ω) : Ω) = (g : Ω ≃ₐ[K] Ω) y := by
  have h : baseChangeArtinMap K E x = topologicalAbelianizationEquiv E Ω
      (topologicalAbelianizationMap (fixingSubgroupHomeomorph E).toMulEquiv.toMonoidHom
        (fixingSubgroupHomeomorph E).continuous ((localClassFieldData K Ω).reciprocityLimit
          (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) ((unitsEquivFixingOpen K E).symm x))) :=
    rfl
  rw [h, ← hg]
  change ((topologicalAbelianizationEquiv E Ω
    (QuotientGroup.mk (fixingSubgroupHomeomorph E g) : TopologicalAbelianization (Ω ≃ₐ[E] Ω)) y :
      maximalAbelianExtension E Ω) : Ω) = _
  rw [topologicalAbelianizationEquiv_mk_apply]
  rfl

end Limit

section Properties

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]

attribute [local instance] isDiscreteModule_units

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in
variable {E} in

theorem isAbelianExtension_fixingOpenSubgroup_of_le {F : IntermediateField K Ω} (h : E ≤ F)
    [FiniteDimensional K F] [IsAbelianGalois E (IntermediateField.extendScalars h)] :
    IsAbelianExtension (fixingOpenSubgroup E) (fixingOpenSubgroup F) := by
  refine ⟨fixingOpenSubgroup_anti h, ?_⟩
  let r : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) →*
      (IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) :=
    (AlgEquiv.restrictNormalHom (IntermediateField.extendScalars h)).comp
      (fixingSubgroupHomeomorph E).toMulEquiv.toMonoidHom
  refine (commutator_le_ker_of_comm r).trans fun σ hσ => ?_
  rw [MonoidHom.mem_ker] at hσ
  rw [Subgroup.mem_subgroupOf, coe_fixingOpenSubgroup, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have := congrArg (fun ρ : IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h =>
    ((ρ ⟨y, (IntermediateField.mem_extendScalars h).2 hy⟩ : IntermediateField.extendScalars h) : Ω)) hσ
  simp only [r] at this
  rw [MonoidHom.comp_apply, AlgEquiv.restrictNormalHom_apply] at this
  exact this

omit [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in
variable {E} in

theorem restrictAb_baseChangeArtinMap_eq_one {F : IntermediateField K Ω} (h : E ≤ F)
    [FiniteDimensional K F] [IsAbelianGalois E (IntermediateField.extendScalars h)] (x : Eˣ)
    (hx : x ∈ (normUnits E (IntermediateField.extendScalars h)).range) :
    restrictAb (IntermediateField.extendScalars h) (le_maximalAbelianExtension _)
      (baseChangeArtinMap K E x) = 1 := by
  have hUV := isAbelianExtension_fixingOpenSubgroup_of_le h
  have := hUV.normal
  set a := (unitsEquivFixingOpen K E).symm x with ha
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) a)
  have hna : a ∈ (norm Ωˣ ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))
      ((fixingOpenSubgroup F : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).range := by
    rw [← map_unitsEquivOfForall_range_norm h (fixingOpenSubgroup E) (fixingOpenSubgroup F) rfl rfl]
      at hx
    obtain ⟨c, hc, hcx⟩ := hx
    have : c = a := by
      rw [ha, MulEquiv.eq_symm_apply]
      exact hcx
    rwa [← this]
  have h1 : abelianizationRestrict hUV
      ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) a) = 1 := by
    rw [ClassFieldData.abelianizationRestrict_reciprocityLimit, MulEquiv.map_eq_one_iff,
      QuotientGroup.eq_one_iff]
    exact hna
  rw [← hg, abelianizationRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    coe_fixingOpenSubgroup, IntermediateField.mem_fixingSubgroup_iff] at h1
  ext y
  rw [restrictAb_apply, baseChangeArtinMap_apply E x g hg, AlgEquiv.one_apply]
  exact h1 y ((IntermediateField.mem_extendScalars h).1 y.2)

end Properties

section Frobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]

attribute [local instance] isDiscreteModule_units

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  [FiniteDimensional K E] in
theorem abelianization_of_injective_of_comm {G : Type*} [Group G] [IsMulCommutative G] :
    Function.Injective (Abelianization.of : G →* Abelianization G) := by
  refine (injective_iff_map_eq_one _).2 fun σ hσ => ?_
  rw [← MonoidHom.mem_ker, Abelianization.ker_of, commutator,
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (fun x _ y _ => mul_comm' y x)] at hσ
  exact hσ

theorem restrictAb_baseChangeArtinMap_uniformizer {ϖ : Eˣ} (hϖ : ord (ϖ : E) = 1) :
    restrictAb (maximalUnramifiedExtension E Ω) maximalUnramifiedExtension_le_maximalAbelianExtension
      (baseChangeArtinMap K E ϖ) = maximalUnramifiedExtensionFrobenius E Ω := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  ext ⟨y, hy⟩
  obtain ⟨E', hE', hyE'⟩ := (mem_maximalUnramifiedExtension_iff (K := E)).1 hy
  obtain ⟨F, h, rfl⟩ : ∃ (F : IntermediateField K Ω) (h : E ≤ F),
      E' = IntermediateField.extendScalars h :=
    ⟨_, _, (extendScalars_restrictScalars' E E').symm⟩
  have := hE'.1
  have := hE'.isGalois
  have hEur := hE'.le_maximalUnramifiedExtension
  have : IsAbelianGalois E (IntermediateField.extendScalars h) :=
    isAbelianGalois_of_le_maximalAbelianExtension _
      (hEur.trans maximalUnramifiedExtension_le_maximalAbelianExtension)
  have : FiniteDimensional K F :=
    (FiniteDimensional.trans K E (IntermediateField.extendScalars h) :)
  have hUV := isAbelianExtension_fixingOpenSubgroup_of_le h
  have := hUV.normal
  have hmc := hUV.isMulCommutative

  set σ₀ : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) :=
    (fixingSubgroupHomeomorph E).symm ((maximalUnramifiedExtensionFrobenius E Ω).liftNormal Ω) with hσ₀
  have hφ : (localClassFieldData K Ω).relDeg (fixingOpenSubgroup E) σ₀ = Multiplicative.ofAdd 1 := by
    rw [relDeg_fixingOpenSubgroup, hσ₀, ContinuousMulEquiv.apply_symm_apply]
    exact (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff _).1
      (AlgEquiv.restrict_liftNormal _ _)
  have hu : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⊓
      (localClassFieldData K Ω).deg.ker ≤ (fixingOpenSubgroup F : Subgroup (Ω ≃ₐ[K] Ω)) := by
    rintro τ ⟨hτU, hτ⟩
    replace hτ : (localClassFieldData K Ω).deg τ = 1 := hτ
    have h1 : (localClassFieldData K Ω).relDeg (fixingOpenSubgroup E) ⟨τ, hτU⟩ = 1 := by
      rw [ClassFieldData.relDeg_eq_iff, one_pow]
      exact hτ
    rw [relDeg_fixingOpenSubgroup, unramifiedDegree_eq_one_iff] at h1
    rw [coe_fixingOpenSubgroup, IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hz' : z ∈ maximalUnramifiedExtension E Ω := hEur ((IntermediateField.mem_extendScalars h).2 hz)
    have := (ker_unramifiedDegree (K := E) (Ω := Ω)) ▸ (MonoidHom.mem_ker.2
      ((unramifiedDegree_eq_one_iff _).2 h1))
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this z hz'
  set a := (unitsEquivFixingOpen K E).symm ϖ with ha
  have hval : (localClassFieldData K Ω).valuation (fixingOpenSubgroup E) a =
      Multiplicative.ofAdd ((1 : ℤ) : ℤ̂) := by
    rw [valuation_fixingOpenSubgroup, ha, MulEquiv.apply_symm_apply, hϖ]
  have key := (localClassFieldData K Ω).reciprocityAbEquiv_symm_of_unramified_of_valuation hUV.le
    (classFieldAxiom_units K Ω) hu hφ a 1 hval
  have hq : Abelianization.of (abelianizationRestrict hUV
      ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) a)) =
      ((localClassFieldData K Ω).reciprocityAbEquiv hUV.le (classFieldAxiom_units K Ω)).symm
        (a : tateZero Ωˣ _ _) := by
    rw [MulEquiv.eq_symm_apply, ClassFieldData.reciprocityAbEquiv_of,
      (localClassFieldData K Ω).abelianizationRestrict_reciprocityLimit (classFieldAxiom_units K Ω) hUV,
      ← (localClassFieldData K Ω).reciprocityAbelianEquiv_apply (classFieldAxiom_units K Ω) hUV,
      MulEquiv.apply_symm_apply]
  rw [key, zpow_one] at hq
  have hq' := abelianization_of_injective_of_comm hq
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) a)
  rw [← hg, abelianizationRestrict_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    coe_fixingOpenSubgroup, IntermediateField.mem_fixingSubgroup_iff] at hq'
  have hyF : y ∈ F := (IntermediateField.mem_extendScalars h).1 hyE'
  have e1 := hq' y hyF
  rw [restrictAb_apply, baseChangeArtinMap_apply E ϖ g hg]
  change (g : Ω ≃ₐ[K] Ω) y = _
  have e2 : ((σ₀ : Ω ≃ₐ[K] Ω) y) = ((maximalUnramifiedExtensionFrobenius E Ω
      (⟨y, hy⟩ : maximalUnramifiedExtension E Ω) : maximalUnramifiedExtension E Ω) : Ω) := by
    rw [← fixingSubgroupHomeomorph_apply, hσ₀, ContinuousMulEquiv.apply_symm_apply]
    exact AlgEquiv.liftNormal_commutes _ Ω (⟨y, hy⟩ : maximalUnramifiedExtension E Ω)
  have e3 : (g : Ω ≃ₐ[K] Ω) y = (σ₀ : Ω ≃ₐ[K] Ω) y := by
    have := congrArg (g : Ω ≃ₐ[K] Ω) e1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
      AlgEquiv.apply_symm_apply] at this
    exact this.symm
  rw [e3, e2]

end Frobenius

section Functoriality

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]

attribute [local instance] isDiscreteModule_units

theorem baseChangeArtinMap_eq : baseChangeArtinMap K E = localArtinMap E Ω := by
  refine eq_localArtinMap_of (fun π hπ => restrictAb_baseChangeArtinMap_uniformizer E hπ) ?_
  intro L _ _ x hx
  obtain ⟨F, h, rfl⟩ : ∃ (F : IntermediateField K Ω) (h : E ≤ F),
      L = IntermediateField.extendScalars h :=
    ⟨_, _, (extendScalars_restrictScalars' E L).symm⟩
  have : FiniteDimensional K F :=
    (FiniteDimensional.trans K E (IntermediateField.extendScalars h) :)
  exact restrictAb_baseChangeArtinMap_eq_one h x hx

theorem localArtinMap_apply_of_mem (x : Eˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ((localArtinMap E Ω x ⟨y, maximalAbelianExtension_le_restrictScalars E hy⟩ :
      maximalAbelianExtension E Ω) : Ω) =
      ((localArtinMap K Ω (normUnits K E x) ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) := by
  rw [← baseChangeArtinMap_eq]
  set a := (unitsEquivFixingOpen K E).symm x with ha
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) a)
  rw [baseChangeArtinMap_apply E x g hg]
  have hE : (E.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  have hN : normUnits K E x = baseUnitsEquiv (norm Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) :
      Subgroup (Ω ≃ₐ[K] Ω)) ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) :
        Subgroup (Ω ≃ₐ[K] Ω)) a) := by
    erw [baseUnitsEquiv_norm E a]
    congr 1
  have hlim := (localClassFieldData K Ω).limitRestrict_reciprocityLimit (classFieldAxiom_units K Ω)
    (le_top : fixingOpenSubgroup E ≤ ⊤) a
  rw [← hg, limitRestrict_mk] at hlim
  rw [hN, localArtinMap_apply, localReciprocityLimit_baseUnitsEquiv, ← hlim, topAbelianizationEquiv_mk,
    topologicalAbelianizationEquiv_mk_apply]

end Functoriality

section Relative

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  {E : IntermediateField K Ω} [FiniteDimensional K E]

attribute [local instance] isDiscreteModule_units

end Relative

end GroundTheory.LocalField
