import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderInfRes
import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderScalars
import GroundTheory.ProfiniteCohomology.LocalClassFormation.UnramifiedRes
import GroundTheory.LocalFields.UnramifiedExistence
import GroundTheory.LocalFields.FiniteExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits groupCohomology GroundTheory.LocalField ValuativeRel
  IntermediateField

section Compare

variable (K K' L L' : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsUnramified K L] [Field K'] [Field L'] [Algebra K K'] [Algebra K L'] [Algebra K' L']
  [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L'] [Normal K L]

theorem h2GalUnitsAddEquiv_unitsRes_unitsInfl (y : groupCohomology (galUnits K L) 2) :
    h2GalUnitsAddEquiv K' L' ((unitsInfl K L L' 2 ≫ unitsRes K K' L' 2).hom y) =
      (unitsResH2 K K' L L').hom (h2GalUnitsAddEquiv K L y) := by
  refine H2_induction_on y fun c => ?_
  rw [h2GalUnitsAddEquiv_H2_class, unitsInfl, unitsRes, ← groupCohomology.map_comp]
  have h1 := congrArg (fun h => ModuleCat.Hom.hom h c) (groupCohomology.H2π_comp_map
    ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).comp (galRestrictScalars K K' L'))
    ((Rep.resFunctor (galRestrictScalars K K' L')).map (unitsInclHom K L L') ≫
      unitsResScalarsHom K K' L'))
  have h2 := congrArg (fun h => ModuleCat.Hom.hom h (cocycles₂IntRepAddEquiv (galUnitsHom K L) c))
    (groupCohomology.H2π_comp_map (galRestrict K K' L L') (unitsResHom K K' L L'))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [h1, h2, h2GalUnitsAddEquiv_H2_class]
  rfl

variable [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [ValuativeRel L']
  [TopologicalSpace L'] [IsNonarchimedeanLocalField L'] [ValuativeExtension K K']
  [ValuativeExtension K' L'] [ValuativeExtension L L'] [FiniteDimensional K K']
  [FiniteDimensional K' L'] [IsUnramified K' L']

theorem unitsInfl_comp_unitsRes_eq_zero (h : Module.finrank K L ∣ Module.finrank K K') :
    unitsInfl K L L' 2 ≫ unitsRes K K' L' 2 = 0 := by
  ext y
  apply (h2GalUnitsAddEquiv K' L').injective
  rw [h2GalUnitsAddEquiv_unitsRes_unitsInfl, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
  apply unramifiedInv_injective K' L'
  rw [unramifiedInv_unitsResH2, map_zero]
  obtain ⟨m, hm⟩ := h
  have hz := (mem_range_unramifiedInv_iff K L (unramifiedInv K L (h2GalUnitsAddEquiv K L y))).1
    ⟨_, rfl⟩
  rw [hm, mul_comm, mul_nsmul, smul_comm, hz, nsmul_zero]

end Compare

section Main

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

theorem finrank_le_natCard_groupCohomology_two_galUnits :
    Module.finrank K L ≤ Nat.card (groupCohomology (galUnits K L) 2) := by
  classical
  set n := Module.finrank K L with hn_def
  have hn : n ≠ 0 := Module.finrank_pos.ne'

  set q := Nat.card 𝓀[K] with hq_def
  set f := Module.finrank 𝓀[K] 𝓀[L] with hf_def
  have hQ : Nat.card 𝓀[L] = q ^ f := by
    have := Fintype.ofFinite 𝓀[K]
    have := Fintype.ofFinite 𝓀[L]
    rw [hq_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[L])]
  have hf : f ≠ 0 := by
    have := ramificationIndex_mul_residueDegree K L
    rw [residueDegree_eq_finrank] at this
    exact right_ne_zero_of_mul (this.trans_ne hn)
  have hq : 1 < q := Finite.one_lt_card

  let Ω := AlgebraicClosure L
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := L) (Ksep := Ω) hn
  rw [hQ, ← pow_mul] at hζ

  let L0 : IntermediateField K Ω := (IsScalarTower.toAlgHom K L Ω).fieldRange
  let eL : L ≃ₐ[K] L0 := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L Ω)
  have : IsGalois K L0 := IsGalois.of_algEquiv eL
  have : FiniteDimensional K L0 := LinearEquiv.finiteDimensional eL.toLinearEquiv
  obtain ⟨hKζ, -, hKζgal, -⟩ :=
    isUnramifiedSubextension_adjoin_spec (K := K) (Ksep := Ω) (mul_ne_zero hf hn) hζ
  have := hKζgal
  have : FiniteDimensional K K⟮ζ⟯ := hKζ.1
  let M0 : IntermediateField K Ω := L0 ⊔ K⟮ζ⟯
  let φL : L →ₐ[K] M0 := (IsScalarTower.toAlgHom K L Ω).codRestrict M0.toSubalgebra
    fun x => (le_sup_left : L0 ≤ M0) ⟨x, rfl⟩
  let : Algebra L M0 := φL.toRingHom.toAlgebra
  have : IsScalarTower K L M0 := IsScalarTower.of_algebraMap_eq fun x => (φL.commutes x).symm
  have : FiniteDimensional L M0 := Module.Finite.of_restrictScalars_finite K L M0
  let := (finiteExtensionStructure L M0).rel
  let := (finiteExtensionStructure L M0).top
  have : IsNonarchimedeanLocalField M0 := finiteExtensionStructure_isNonarchimedeanLocalField L M0
  have : ValuativeExtension L M0 := finiteExtensionStructure_valuativeExtension L M0
  have : ValuativeExtension K M0 := valuativeExtension_trans K L M0
  let ζM : M0 := ⟨ζ, (le_sup_right : K⟮ζ⟯ ≤ M0) (mem_adjoin_simple_self K ζ)⟩
  have hζM : IsPrimitiveRoot ζM (q ^ (f * n) - 1) :=
    (IsPrimitiveRoot.map_iff_of_injective (f := M0.val) M0.val.injective).1 hζ

  have hF := isUnramifiedSubextension_adjoin (K := L) (Ksep := M0) hn
    (show IsPrimitiveRoot ζM (Nat.card 𝓀[L] ^ n - 1) by rw [hQ, ← pow_mul]; exact hζM)
  have htop : L⟮ζM⟯ = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hle : M0 ≤ ((L⟮ζM⟯).restrictScalars K).map M0.val := by
      refine sup_le ?_ ?_
      · rintro _ ⟨y, rfl⟩
        exact ⟨algebraMap L M0 y, (L⟮ζM⟯).algebraMap_mem y, rfl⟩
      · rw [adjoin_simple_le_iff]
        exact ⟨ζM, mem_adjoin_simple_self L ζM, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have : IsUnramified L M0 := by
    have h1 : IsUnramified L L⟮ζM⟯ := (isUnramified_iff _ _).2 hF.1.ramificationIndex_eq_one
    have hfr : Module.finrank L⟮ζM⟯ M0 = 1 := by
      have h := Module.finrank_mul_finrank L L⟮ζM⟯ M0
      have h' : Module.finrank L L⟮ζM⟯ = Module.finrank L M0 := by
        rw [htop]
        exact IntermediateField.finrank_top'
      rw [h'] at h
      exact (Nat.mul_eq_left Module.finrank_pos.ne').1 h
    have h2 : IsUnramified L⟮ζM⟯ M0 := by
      rw [isUnramified_iff]
      have := ramificationIndex_mul_residueDegree L⟮ζM⟯ M0
      rw [hfr] at this
      exact Nat.eq_one_of_mul_eq_one_right this
    exact (isUnramified_tower_iff L L⟮ζM⟯ M0).2 ⟨h1, h2⟩

  have hdvd : q ^ n - 1 ∣ q ^ (f * n) - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (q ^ n) 1 f
    rwa [one_pow, ← pow_mul, mul_comm] at this
  have hpos : 0 < q ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn hq)
  set k := (q ^ (f * n) - 1) / (q ^ n - 1) with hk_def
  have hk0 : k ≠ 0 := (Nat.div_pos (Nat.le_of_dvd
    (Nat.sub_pos_of_lt (Nat.one_lt_pow (mul_ne_zero hf hn) hq)) hdvd) hpos).ne'
  have hkdvd : k ∣ q ^ (f * n) - 1 := Nat.div_dvd_of_dvd hdvd
  have hζk : IsPrimitiveRoot (ζM ^ k) (q ^ n - 1) := by
    have := hζM.pow_of_dvd hk0 hkdvd
    rwa [hk_def, Nat.div_div_self hdvd
      (Nat.sub_pos_of_lt (Nat.one_lt_pow (mul_ne_zero hf hn) hq)).ne'] at this
  obtain ⟨hE, hEn, hEgal, hEcyc, -⟩ :=
    isUnramifiedSubextension_adjoin_spec (K := K) (Ksep := M0) hn hζk
  have := hEgal
  have := hEcyc
  have : FiniteDimensional K K⟮ζM ^ k⟯ := hE.1
  have : IsUnramified K K⟮ζM ^ k⟯ := (isUnramified_iff _ _).2 hE.ramificationIndex_eq_one

  have hvanish := unitsInfl_comp_unitsRes_eq_zero K L K⟮ζM ^ k⟯ M0 (by rw [hEn])
  have := finite_groupCohomology_two_galUnits (K := K) (L := L)
  have hle := natCard_le_of_unitsInfl_comp_unitsRes_eq_zero K K⟮ζM ^ k⟯ L M0 hvanish
  rw [natCard_groupCohomology_two_galUnits_of_isCyclic, hEn] at hle
  exact hle

theorem natCard_groupCohomology_two_galUnits :
    Nat.card (groupCohomology (galUnits K L) 2) = Module.finrank K L :=
  le_antisymm (Nat.le_of_dvd Module.finrank_pos natCard_groupCohomology_two_galUnits_dvd)
    finrank_le_natCard_groupCohomology_two_galUnits

end Main

end GroundTheory.ProfCoh
