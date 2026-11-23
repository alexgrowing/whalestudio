import Mathlib
import GroundTheory.LocalFields.LocalAxiom
import GroundTheory.LocalFields.LocalReciprocityLimitAbstract

namespace GroundTheory.LocalField

open Abstract ValuativeRel

section Transport

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

noncomputable def transportReciprocity {K' L' : OpenSubgroup (Ω ≃ₐ[K] Ω)} (hLK : L' ≤ K')
    [((L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K').Normal] {Γ M : Type*} [Group Γ] [CommGroup M]
    (e : (K' : Subgroup (Ω ≃ₐ[K] Ω)) ⧸ (L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K' ≃* Γ)
    (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) ≃* M) (N : Subgroup M)
    (hN : (norm Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) (L' : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) →* M) = N) :
    Abelianization Γ ≃* M ⧸ N :=
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  e.abelianizationCongr.symm.trans
    (((localClassFieldData K Ω).reciprocityAbEquiv hLK (classFieldAxiom_units K Ω)).trans
      (QuotientGroup.congr _ _ u hN))

theorem transportReciprocity_symm_mk {K' L' : OpenSubgroup (Ω ≃ₐ[K] Ω)} (hLK : L' ≤ K')
    [((L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K').Normal] {Γ M : Type*} [Group Γ] [CommGroup M]
    (e : (K' : Subgroup (Ω ≃ₐ[K] Ω)) ⧸ (L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K' ≃* Γ)
    (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) ≃* M) (N : Subgroup M)
    (hN : (norm Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) (L' : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) →* M) = N) (a : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω))) :
    haveI := isDiscreteModule_units (K := K) (Ω := Ω)
    (transportReciprocity hLK e u N hN).symm (u a : M ⧸ N) =
      e.abelianizationCongr (((localClassFieldData K Ω).reciprocityAbEquiv hLK
        (classFieldAxiom_units K Ω)).symm (a : tateZero Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω))
          (L' : Subgroup (Ω ≃ₐ[K] Ω)))) := by
  simp only [transportReciprocity, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  congr 2
  rw [QuotientGroup.congr_symm, QuotientGroup.congr_mk, MulEquiv.symm_apply_apply]

end Transport

section Base

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

noncomputable def restrictTop :
    ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) →* (L ≃ₐ[K] L) :=
  (AlgEquiv.restrictNormalHom L).comp (⊤ : Subgroup (Ω ≃ₐ[K] Ω)).subtype

@[simp]
theorem restrictTop_apply (σ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    restrictTop L σ = (σ : Ω ≃ₐ[K] Ω).restrictNormal L :=
  rfl

theorem restrictTop_surjective : Function.Surjective (restrictTop L) := fun τ => by
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω) τ
  exact ⟨⟨σ, Subgroup.mem_top σ⟩, hσ⟩

theorem ker_restrictTop :
    (restrictTop L).ker = (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) := by
  ext σ
  have hc : ∀ y : L, ((((σ : Ω ≃ₐ[K] Ω).restrictNormal L) y : L) : Ω) = (σ : Ω ≃ₐ[K] Ω) y :=
    fun y => AlgEquiv.restrictNormal_commutes _ _ y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, coe_fixingOpenSubgroup,
    IntermediateField.mem_fixingSubgroup_iff, restrictTop_apply]
  constructor
  · intro h x hx
    have := congrArg (fun τ : L ≃ₐ[K] L => ((τ ⟨x, hx⟩ : L) : Ω)) h
    simp only [hc, AlgEquiv.one_apply] at this
    exact this
  · intro h
    ext x
    rw [hc, AlgEquiv.one_apply]
    exact h x x.2

instance normal_fixingOpenSubgroup_top :
    ((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal := by
  rw [← ker_restrictTop]
  exact MonoidHom.normal_ker _

noncomputable def baseQuotientEquiv :
    ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⧸
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
          ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_restrictTop L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (restrictTop_surjective L))

@[simp]
theorem baseQuotientEquiv_mk (σ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    baseQuotientEquiv L (σ : _ ⧸ _) = (σ : Ω ≃ₐ[K] Ω).restrictNormal L :=
  rfl

theorem map_baseUnitsEquiv_range_norm :
    (norm Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (baseUnitsEquiv (K := K) (Ω := Ω) : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ) =
      (normUnits K L).range := by
  haveI : (L.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, (baseUnitsEquiv_norm L a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨(fixedModuleUnitsEquiv L).symm b, rfl⟩, ?_⟩
    change baseUnitsEquiv (Abstract.norm Ωˣ ⊤ L.fixingSubgroup _) = _
    rw [baseUnitsEquiv_norm, MulEquiv.apply_symm_apply]

noncomputable def localReciprocity : Abelianization (L ≃ₐ[K] L) ≃* Kˣ ⧸ (normUnits K L).range :=
  transportReciprocity (K' := ⊤) (L' := fixingOpenSubgroup L) le_top (baseQuotientEquiv L)
    baseUnitsEquiv (normUnits K L).range (map_baseUnitsEquiv_range_norm L)

theorem localReciprocity_symm_mk_baseUnitsEquiv
    (a : fixedModule Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    haveI := isDiscreteModule_units (K := K) (Ω := Ω)
    (localReciprocity L).symm (baseUnitsEquiv a : Kˣ ⧸ (normUnits K L).range) =
      (baseQuotientEquiv L).abelianizationCongr
        (((localClassFieldData K Ω).reciprocityAbEquiv (le_top : fixingOpenSubgroup L ≤ ⊤)
          (classFieldAxiom_units K Ω)).symm (a : tateZero Ωˣ _ _)) :=
  transportReciprocity_symm_mk _ _ _ _ _ a

end Base

section Frobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem inertiaDegree_top_unramifiedDegree :
    inertiaDegree (unramifiedDegree K Ω)
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) = 1 := by
  rw [inertiaDegree]
  change ((⊤ : Subgroup (Ω ≃ₐ[K] Ω)).map (unramifiedDegree K Ω)).index = 1
  rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top_of_surjective _ unramifiedDegree_surjective,
    Subgroup.index_top]

theorem valuation_top_localClassFieldData
    (a : fixedModule Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    (localClassFieldData K Ω).valuation ⊤ a =
      Multiplicative.ofAdd ((ord ((baseUnitsEquiv a : Kˣ) : K) : ℤ) : ℤ̂) := by
  have h := (localClassFieldData K Ω).valuation_pow ⊤ a
  rw [localClassFieldData_deg, inertiaDegree_top_unramifiedDegree, pow_one] at h
  rw [h]
  erw [norm_self]
  rfl

variable (K Ω) in

noncomputable def unramifiedFrobenius (L : IntermediateField K Ω) [Normal K L] : L ≃ₐ[K] L :=
  ((maximalUnramifiedExtensionFrobenius K Ω).liftNormal Ω).restrictNormal L

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

theorem localReciprocity_symm_mk_of_le_maximalUnramifiedExtension
    (hL : L ≤ maximalUnramifiedExtension K Ω) (x : Kˣ) :
    (localReciprocity L).symm (x : Kˣ ⧸ (normUnits K L).range) =
      Abelianization.of (unramifiedFrobenius K Ω L) ^ ord (x : K) := by
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  set σ := (maximalUnramifiedExtensionFrobenius K Ω).liftNormal Ω with hσdef
  have hσ : σ.restrictNormal (maximalUnramifiedExtension K Ω) =
      maximalUnramifiedExtensionFrobenius K Ω := AlgEquiv.restrict_liftNormal _ _
  obtain ⟨a, rfl⟩ := (baseUnitsEquiv (K := K) (Ω := Ω)).surjective x
  rw [localReciprocity_symm_mk_baseUnitsEquiv]
  have hu : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⊓
      (localClassFieldData K Ω).deg.ker ≤ (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)) := by
    rw [localClassFieldData_deg, ker_unramifiedDegree, coe_fixingOpenSubgroup]
    exact inf_le_right.trans (IntermediateField.fixingSubgroup_antitone hL)
  have hφ : (localClassFieldData K Ω).relDeg ⊤ ⟨σ, Subgroup.mem_top σ⟩ = Multiplicative.ofAdd 1 := by
    rw [ClassFieldData.relDeg_eq_iff, localClassFieldData_deg, inertiaDegree_top_unramifiedDegree,
      pow_one]
    exact (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff σ).1 hσ
  rw [(localClassFieldData K Ω).reciprocityAbEquiv_symm_of_unramified_of_valuation le_top
    (classFieldAxiom_units K Ω) hu hφ a _ (valuation_top_localClassFieldData a), map_zpow]
  rfl

end Frobenius

section Relative

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in

theorem finiteDimensional_of_le' {E F : IntermediateField K Ω} (h : E ≤ F) [FiniteDimensional K F] :
    FiniteDimensional K E :=
  FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap
    fun x y hxy => Subtype.ext (congrArg (fun z : F => (z : Ω)) hxy)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in

theorem fixingOpenSubgroup_anti {L F : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K F] (h : L ≤ F) : fixingOpenSubgroup F ≤ fixingOpenSubgroup L :=
  fun _ hx => IntermediateField.fixingSubgroup_antitone h hx

variable {E F : IntermediateField K Ω} (h : E ≤ F) [FiniteDimensional K F]
  [IsGalois E (IntermediateField.extendScalars h)]

theorem map_unitsEquivOfForall_range_norm (K' L' : OpenSubgroup (Ω ≃ₐ[K] Ω))
    (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L') :
    (norm Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) (L' : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (unitsEquivOfForall (K' : Subgroup (Ω ≃ₐ[K] Ω)) E (mem_iff_forall_of_fixingSubgroup_eq _ hK) :
        fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) →* Eˣ) =
      (normUnits E (IntermediateField.extendScalars h)).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, (unitsEquivOfForall_norm (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨(unitsEquivOfForall (L' : Subgroup (Ω ≃ₐ[K] Ω)) (IntermediateField.extendScalars h)
      (mem_extendScalars_iff_forall _ h hL)).symm b, rfl⟩, ?_⟩
    change unitsEquivOfForall _ E _ (norm Ωˣ _ _ _) = _
    rw [unitsEquivOfForall_norm (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL, MulEquiv.apply_symm_apply]

noncomputable def relReciprocityOfFixingSubgroups (K' L' : OpenSubgroup (Ω ≃ₐ[K] Ω)) (hK : E.fixingSubgroup = K')
    (hL : F.fixingSubgroup = L') :
    Abelianization (IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) ≃*
      Eˣ ⧸ (normUnits E (IntermediateField.extendScalars h)).range :=
  haveI := (galoisTateModel (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL).normal
  transportReciprocity (K' := K') (L' := L')
    (fun _ hx => (galoisTateModel (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL).le hx)
    (galoisTateModel (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL).quotientEquiv
    (unitsEquivOfForall (K' : Subgroup (Ω ≃ₐ[K] Ω)) E (mem_iff_forall_of_fixingSubgroup_eq _ hK))
    _ (map_unitsEquivOfForall_range_norm h K' L' hK hL)

noncomputable def relLocalReciprocity :
    Abelianization (IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) ≃*
      Eˣ ⧸ (normUnits E (IntermediateField.extendScalars h)).range :=
  haveI := finiteDimensional_of_le' h
  relReciprocityOfFixingSubgroups h (fixingOpenSubgroup E) (fixingOpenSubgroup F) rfl rfl

end Relative

section NormSquare

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {E F : IntermediateField K Ω} (h : E ≤ F) [FiniteDimensional K F]
  [IsGalois E (IntermediateField.extendScalars h)]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

noncomputable def galRestrictField (hLF : L ≤ F) :
    (IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) →* (L ≃ₐ[K] L) :=
  haveI := finiteDimensional_of_le' h
  haveI := (galoisTateModel (fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)) (fixingOpenSubgroup F)
    h rfl rfl).normal
  (baseQuotientEquiv L).toMonoidHom.comp
    ((galRestrict (le_top : fixingOpenSubgroup E ≤ ⊤)
      (fixingOpenSubgroup_anti hLF)).comp
      (galoisTateModel (fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)) (fixingOpenSubgroup F)
        h rfl rfl).quotientEquiv.symm.toMonoidHom)

end NormSquare

section ConjSquare

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in

theorem fixingSubgroup_map_conj (σ : Ω ≃ₐ[K] Ω) (E : IntermediateField K Ω) :
    (E.map (σ : Ω →ₐ[K] Ω)).fixingSubgroup = E.fixingSubgroup.map (MulAut.conj σ).toMonoidHom := by
  ext τ
  rw [mem_map_conj, IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hτ y hy
    have := hτ (σ y) ⟨y, hy, rfl⟩
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact this
  · rintro hτ _ ⟨y, hy, rfl⟩
    have := hτ y hy
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at this
    exact this

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in
theorem fixingSubgroup_eq_conjOpen (σ : Ω ≃ₐ[K] Ω) {E E₂ : IntermediateField K Ω}
    [FiniteDimensional K E] (hE : E.map (σ : Ω →ₐ[K] Ω) = E₂) :
    E₂.fixingSubgroup = (conjOpen σ (fixingOpenSubgroup E) : Subgroup (Ω ≃ₐ[K] Ω)) := by
  rw [← hE, fixingSubgroup_map_conj]
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in
theorem apply_mem_of_map_eq (σ : Ω ≃ₐ[K] Ω) {E E₂ : IntermediateField K Ω}
    (hE : E.map (σ : Ω →ₐ[K] Ω) = E₂) {y : Ω} (hy : y ∈ E) : σ y ∈ E₂ := by
  rw [← hE]
  exact ⟨y, hy, rfl⟩

variable {E F : IntermediateField K Ω} (h : E ≤ F) [FiniteDimensional K F]
  [IsGalois E (IntermediateField.extendScalars h)] (σ : Ω ≃ₐ[K] Ω)
  {E₂ F₂ : IntermediateField K Ω} (h₂ : E₂ ≤ F₂) [FiniteDimensional K F₂]
  [IsGalois E₂ (IntermediateField.extendScalars h₂)]
  (hE : E.map (σ : Ω →ₐ[K] Ω) = E₂) (hF : F.map (σ : Ω →ₐ[K] Ω) = F₂)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω]
  [FiniteDimensional K F] [IsGalois E (IntermediateField.extendScalars h)] [FiniteDimensional K F₂]
  [IsGalois E₂ (IntermediateField.extendScalars h₂)] in
include hE in

noncomputable def conjUnits : Eˣ →* E₂ˣ :=
  Units.map (((σ : Ω →+* Ω).comp (algebraMap E Ω)).codRestrict E₂ fun y =>
    apply_mem_of_map_eq σ hE y.2)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω]
  [FiniteDimensional K F] [IsGalois E (IntermediateField.extendScalars h)] [FiniteDimensional K F₂]
  [IsGalois E₂ (IntermediateField.extendScalars h₂)] in
@[simp]
theorem coe_conjUnits (x : Eˣ) : (((conjUnits σ hE x : E₂ˣ) : E₂) : Ω) = σ (x : Ω) :=
  rfl

omit [IsGalois E₂ (IntermediateField.extendScalars h₂)] in
include hE hF in
theorem conj_mem_extendScalars (x : IntermediateField.extendScalars h) :
    σ (x : Ω) ∈ IntermediateField.extendScalars h₂ :=
  (IntermediateField.mem_extendScalars h₂).2
    (apply_mem_of_map_eq σ hF ((IntermediateField.mem_extendScalars h).1 x.2))

noncomputable def conjGal :
    (IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) →*
      (IntermediateField.extendScalars h₂ ≃ₐ[E₂] IntermediateField.extendScalars h₂) :=
  haveI := finiteDimensional_of_le' h
  haveI := (galoisTateModel (fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)) (fixingOpenSubgroup F)
    h rfl rfl).normal
  (galoisTateModel (conjOpen σ (fixingOpenSubgroup E) : Subgroup (Ω ≃ₐ[K] Ω))
    (conjOpen σ (fixingOpenSubgroup F)) h₂ (fixingSubgroup_eq_conjOpen σ hE)
    (fixingSubgroup_eq_conjOpen σ hF)).quotientEquiv.toMonoidHom.comp
    ((galConj σ (fixingOpenSubgroup E) (fixingOpenSubgroup F)).comp
      (galoisTateModel (fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)) (fixingOpenSubgroup F)
        h rfl rfl).quotientEquiv.symm.toMonoidHom)

theorem conjGal_apply (τ : IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h)
    (x : IntermediateField.extendScalars h) :
    ((conjGal h σ h₂ hE hF τ ⟨σ x, conj_mem_extendScalars h σ h₂ hE hF x⟩ :
      IntermediateField.extendScalars h₂) : Ω) = σ ((τ x : IntermediateField.extendScalars h) : Ω) := by
  haveI := finiteDimensional_of_le' h
  set T := galoisTateModel (fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)) (fixingOpenSubgroup F)
    h rfl rfl
  set T₂ := galoisTateModel (conjOpen σ (fixingOpenSubgroup E) : Subgroup (Ω ≃ₐ[K] Ω))
    (conjOpen σ (fixingOpenSubgroup F)) h₂ (fixingSubgroup_eq_conjOpen σ hE)
    (fixingSubgroup_eq_conjOpen σ hF)
  haveI := T.normal
  obtain ⟨ρ, rfl⟩ := T.surjective_hom τ
  have e : T.quotientEquiv.symm (T.hom ρ) = (ρ : _ ⧸ _) := by
    rw [MulEquiv.symm_apply_eq, TateModel.quotientEquiv_mk]
  have hρ : ∀ y : IntermediateField.extendScalars h,
      ((T.hom ρ y : IntermediateField.extendScalars h) : Ω) = (ρ : Ω ≃ₐ[K] Ω) y :=
    fun y => coe_restrictHom_apply _ h rfl ρ y
  have hρ₂ : ∀ (ρ₂ : (conjOpen σ (fixingOpenSubgroup E) : Subgroup (Ω ≃ₐ[K] Ω)))
      (y : IntermediateField.extendScalars h₂),
      ((T₂.hom ρ₂ y : IntermediateField.extendScalars h₂) : Ω) = (ρ₂ : Ω ≃ₐ[K] Ω) y :=
    fun ρ₂ y => coe_restrictHom_apply _ h₂ (fixingSubgroup_eq_conjOpen σ hE) ρ₂ y
  rw [hρ]
  change ((T₂.quotientEquiv (galConj σ (fixingOpenSubgroup E) (fixingOpenSubgroup F)
    (T.quotientEquiv.symm (T.hom ρ))) ⟨σ x, _⟩ : IntermediateField.extendScalars h₂) : Ω) = _
  rw [e, galConj_mk, TateModel.quotientEquiv_mk, hρ₂]
  simp [AlgEquiv.mul_apply]

end ConjSquare

end GroundTheory.LocalField
