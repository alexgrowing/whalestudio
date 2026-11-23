import Mathlib
import GroundTheory.LocalFields.ConductorLubinTate
import GroundTheory.LocalFields.ConductorTransport
import GroundTheory.LocalFields.LocalArtinMap
import GroundTheory.LocalFields.KroneckerWeber

noncomputable section

open ValuativeRel GroundTheory.LocalField.FormalGroup GroundTheory.LocalField.Abstract

namespace GroundTheory.LocalField

section Bridge

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

include hf in

theorem restrictAb_localArtinMap_lubinTate {n : ℕ} (hn : 0 < n) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsGalois K E] (hE : E ≤ maximalUnramifiedExtension K Ω)
    [IsAbelianGalois K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)]
    (u : 𝒪[K]ˣ) (k : ℤ) (τ : Ω ≃ₐ[K] Ω)
    (hτd : unramifiedDegree K Ω τ = Multiplicative.ofAdd (k : ℤ̂))
    (hτ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) :
    restrictAb (lubinTateField Ω hπ hf n ⊔ E) (le_maximalAbelianExtension _)
        (localArtinMap K Ω (unitUniformizerPow hπ u k)) =
      AlgEquiv.restrictNormalHom (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) τ := by
  rw [restrictAb_localArtinMap]
  apply (bijective_abelianizationOf _).1
  rw [of_localReciprocityAbelian_symm]
  have hrec := reciprocity_lubinTate_sup hπ hf hn E hE u k τ hτd hτ
  have h2 := localReciprocity_symm_mk_baseUnitsEquiv (lubinTateField Ω hπ hf n ⊔ E)
    (baseUnitsEquiv.symm (unitUniformizerPow hπ u k))
  rw [MulEquiv.apply_symm_apply] at h2
  rw [h2]
  have h3 : ((localClassFieldData K Ω).reciprocityAbEquiv
      (le_top : fixingOpenSubgroup (lubinTateField Ω hπ hf n ⊔ E) ≤ ⊤)
      (classFieldAxiom_units K Ω)).symm
        ((baseUnitsEquiv.symm (unitUniformizerPow hπ u k) : fixedModule Ωˣ
          ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) : tateZero Ωˣ _ _) =
      Abelianization.of (QuotientGroup.mk
        (⟨τ, by simp⟩ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)))) := by
    rw [MulEquiv.symm_apply_eq, ClassFieldData.reciprocityAbEquiv_of]
    exact hrec.symm
  rw [h3, abelianizationCongr_of, baseQuotientEquiv_mk]
  rfl

section Compositum

variable {n : ℕ} (hn : 0 < n) {E : IntermediateField K Ω} [FiniteDimensional K E] [IsGalois K E]
  (hE : IsUnramifiedSubextension E)

include hn hE in

theorem mem_upperRamificationGroup_lubinTateField_sup {v : ℝ} (hv : -1 < v)
    (σ : (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) ≃ₐ[K]
      (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)) :
    σ ∈ upperRamificationGroup K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) v ↔
      restrictAut le_sup_right σ = 1 ∧
        restrictAut le_sup_left σ ∈ lubinTateUnitSubgroup hπ hf n ⌈v⌉.toNat := by
  have hT := map_upperRamificationGroup_restrictAut
    (le_sup_left : lubinTateField Ω hπ hf n ≤ lubinTateField Ω hπ hf n ⊔ E) v
  rw [upperRamificationGroup_lubinTateField] at hT
  have hEv := map_upperRamificationGroup_restrictAut
    (le_sup_right : E ≤ lubinTateField Ω hπ hf n ⊔ E) v
  rw [upperRamificationGroup_eq_bot_of_ramificationIndex_eq_one hE.ramificationIndex_eq_one hv] at hEv
  constructor
  · intro hσ
    refine ⟨?_, ?_⟩
    · have := Subgroup.mem_map_of_mem (restrictAut (le_sup_right :
        E ≤ lubinTateField Ω hπ hf n ⊔ E)) hσ
      rwa [hEv, Subgroup.mem_bot] at this
    · rw [← hT]
      exact Subgroup.mem_map_of_mem _ hσ
  · rintro ⟨h1, h2⟩
    rw [← hT] at h2
    obtain ⟨σ', hσ', he⟩ := h2
    have h1' : restrictAut (le_sup_right : E ≤ lubinTateField Ω hπ hf n ⊔ E) σ' = 1 := by
      have := Subgroup.mem_map_of_mem (restrictAut (le_sup_right :
        E ≤ lubinTateField Ω hπ hf n ⊔ E)) hσ'
      rwa [hEv, Subgroup.mem_bot] at this
    have : σ' = σ := (bijective_restrictAut_prod hπ hf hn hE).1 (Prod.ext he (h1'.trans h1.symm))
    exact this ▸ hσ'

include hn hE in

theorem restrictAut_localArtinMap_unitsIncl
    [IsAbelianGalois K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)] (u : 𝒪[K]ˣ) :
    restrictAut le_sup_right (restrictAb (lubinTateField Ω hπ hf n ⊔ E) (le_maximalAbelianExtension _)
        (localArtinMap K Ω (unitsIncl K u))) = 1 ∧
      lubinTateChar hπ hf n le_sup_left (restrictAb (lubinTateField Ω hπ hf n ⊔ E)
        (le_maximalAbelianExtension _) (localArtinMap K Ω (unitsIncl K u))) = unitsMk π n u⁻¹ := by
  obtain ⟨τ, hτd, hτ⟩ := exists_lubinTate_action (Ω := Ω) hπ hf hn u 0
  have hx : unitsIncl K u = unitUniformizerPow hπ u 0 := by
    rw [unitUniformizerPow_eq, zpow_zero, one_mul]
  rw [hx, restrictAb_localArtinMap_lubinTate hπ hf hn E hE.le_maximalUnramifiedExtension u 0 τ hτd hτ]
  have hτ1 : τ ∈ (maximalUnramifiedExtension K Ω).fixingSubgroup := by
    rw [← ker_unramifiedDegree, MonoidHom.mem_ker, hτd]
    simp
  refine ⟨?_, ?_⟩
  · apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [restrictAut_apply, AlgEquiv.one_apply, AlgEquiv.restrictNormalHom_apply]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ1 x
      (hE.le_maximalUnramifiedExtension x.2)
  · apply Units.ext
    rw [lubinTateChar_eq_of_apply hπ hf le_sup_left _ ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]), coe_unitsMk]
    intro x hx
    rw [AlgEquiv.restrictNormalHom_apply, ← hτ x hx, lubinTateGalPointMap_val]

include hn hE in

theorem map_unitFiltrationUnits_lubinTateField_sup
    [IsAbelianGalois K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)] (j : ℕ) :
    (unitFiltrationUnits K j).map ((restrictAb (lubinTateField Ω hπ hf n ⊔ E)
        (le_maximalAbelianExtension _)).comp (localArtinMap K Ω)) =
      upperRamificationGroup K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) j := by
  ext σ
  have hj : (-1 : ℝ) < j := by have := j.cast_nonneg (α := ℝ); linarith
  rw [mem_upperRamificationGroup_lubinTateField_sup hπ hf hn hE hj, Int.ceil_natCast,
    Int.toNat_natCast, Subgroup.mem_map]
  constructor
  · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨h1, h2⟩ := restrictAut_localArtinMap_unitsIncl hπ hf hn hE u
    refine ⟨h1, ?_⟩
    rw [lubinTateUnitSubgroup, Subgroup.mem_comap]
    exact ⟨u⁻¹, inv_mem hu, h2.symm⟩
  · rintro ⟨h1, w, hw, hwσ⟩
    refine ⟨unitsIncl K w⁻¹, ⟨w⁻¹, inv_mem hw, rfl⟩, ?_⟩
    obtain ⟨g1, g2⟩ := restrictAut_localArtinMap_unitsIncl hπ hf hn hE w⁻¹
    apply (bijective_restrictAut_prod hπ hf hn hE).1
    refine Prod.ext ?_ (g1.trans h1.symm)
    apply (lubinTateGalEquiv hπ hf n).injective
    change lubinTateChar hπ hf n le_sup_left _ = _
    rw [MonoidHom.comp_apply, g2, inv_inv]
    exact hwσ

end Compositum

end Bridge

section Abelian

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem restrictAb_eq_restrictAut_comp {L M : IntermediateField K Ω} [Normal K L] [Normal K M]
    (h : L ≤ M) (hM : M ≤ maximalAbelianExtension K Ω) :
    restrictAb L (h.trans hM) = (restrictAut h).comp (restrictAb M hM) := by
  refine MonoidHom.ext fun σ => AlgEquiv.ext fun x => Subtype.ext ?_
  rw [MonoidHom.comp_apply, restrictAut_apply, restrictAb_apply, restrictAb_apply]

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

theorem exists_le_lubinTateField_sup :
    ∃ (π : 𝒪[K]) (hπ : Irreducible π) (n : ℕ) (E : IntermediateField K Ω),
      0 < n ∧ IsUnramifiedSubextension E ∧
        L ≤ lubinTateField Ω hπ (isLubinTateSeries_ltPoly π) n ⊔ E := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨n, m, hLM⟩ := exists_le_lubinTateField_sup_unramifiedTower hπ (isLubinTateSeries_ltPoly π) L
  exact ⟨π, hπ, n + 1, unramifiedTower K Ω m, n.succ_pos, isUnramifiedSubextension_unramifiedTower m,
    hLM⟩

theorem map_unitFiltrationUnits_restrictAb_localArtinMap (n : ℕ) :
    (unitFiltrationUnits K n).map
        ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)) =
      upperRamificationGroup K L n := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨π, hπ, k, E, hk, hE, hLM⟩ := exists_le_lubinTateField_sup L (Ω := Ω)
  have := hE.1
  have := hE.isGalois
  have := isAbelianGalois_lubinTateField_sup hπ (isLubinTateSeries_ltPoly π) hk hE
  rw [restrictAb_eq_restrictAut_comp hLM (le_maximalAbelianExtension _), MonoidHom.comp_assoc,
    ← Subgroup.map_map, map_unitFiltrationUnits_lubinTateField_sup hπ (isLubinTateSeries_ltPoly π) hk hE,
    map_upperRamificationGroup_restrictAut hLM]

theorem upperRamificationGroup_eq_ceil (v : ℝ) :
    upperRamificationGroup K L v = upperRamificationGroup K L ⌈v⌉ := by
  rcases le_or_gt v (-1) with hv | hv
  · have hc : ((⌈v⌉ : ℤ) : ℝ) ≤ -1 := by
      have : ⌈v⌉ ≤ -1 := Int.ceil_le.2 (by push_cast; exact hv)
      exact_mod_cast this
    rw [upperRamificationGroup_of_nonpos (by linarith), lowerRamificationGroupReal_eq_top hv,
      upperRamificationGroup_of_nonpos (by linarith), lowerRamificationGroupReal_eq_top hc]
  · have : IsSepClosed Ω := IsSepClosure.sep_closed K
    obtain ⟨π, hπ, k, E, hk, hE, hLM⟩ := exists_le_lubinTateField_sup L (Ω := Ω)
    have := hE.1
    have := hE.isGalois
    have hv' : -1 < ((⌈v⌉ : ℤ) : ℝ) := hv.trans_le (Int.le_ceil v)
    rw [← map_upperRamificationGroup_restrictAut hLM v,
      ← map_upperRamificationGroup_restrictAut hLM (⌈v⌉ : ℝ)]
    congr 1
    ext σ
    rw [mem_upperRamificationGroup_lubinTateField_sup hπ _ hk hE hv,
      mem_upperRamificationGroup_lubinTateField_sup hπ _ hk hE hv', Int.ceil_intCast]

end Abelian

end GroundTheory.LocalField
