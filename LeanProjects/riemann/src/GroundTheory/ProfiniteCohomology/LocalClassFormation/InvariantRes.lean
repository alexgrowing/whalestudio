import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.InvariantSplit
import GroundTheory.Brauer.BaseChangeRestriction
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

section Bridge

variable (K K' L L' : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsUnramified K L] [Field K'] [Field L'] [Algebra K K'] [Algebra K L'] [Algebra K' L']
  [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']

noncomputable def unitsResHomU :
    Rep.res (galRestrict K K' L L') (galUnits K L) ⟶ galUnits K' L' :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Lˣ) (B := Additive L'ˣ)
    (MonoidHom.toAdditive (Units.map ((algebraMap L L' : L →+* L') : L →* L'))), fun σ => by
      ext x
      exact algebraMap_galRestrict_apply K K' L L' σ _⟩

@[simp]
theorem unitsResHomU_hom_apply (x : Additive Lˣ) :
    ((Additive.toMul (α := L'ˣ) ((unitsResHomU K K' L L').hom x) : L'ˣ) : L') =
      algebraMap L L' ((Additive.toMul (α := Lˣ) x : Lˣ) : L) :=
  rfl

noncomputable abbrev unitsResH2Lift :
    groupCohomology (galUnits K L) 2 ⟶ groupCohomology (galUnits K' L') 2 :=
  groupCohomology.map (galRestrict K K' L L') (unitsResHomU K K' L L') 2

theorem h2GalUnitsAddEquiv_unitsResH2Lift (y : groupCohomology (galUnits K L) 2) :
    h2GalUnitsAddEquiv K' L' ((unitsResH2Lift K K' L L').hom y) =
      (unitsResH2 K K' L L').hom (h2GalUnitsAddEquiv K L y) := by
  refine groupCohomology.H2_induction_on y fun c => ?_
  have h1 := congrArg (fun h => ModuleCat.Hom.hom h c)
    (groupCohomology.H2π_comp_map (galRestrict K K' L L') (unitsResHomU K K' L L'))
  have h2 := congrArg (fun h => ModuleCat.Hom.hom h (cocycles₂IntRepAddEquiv (galUnitsHom K L) c))
    (groupCohomology.H2π_comp_map (galRestrict K K' L L') (unitsResHom K K' L L'))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [h1, h2GalUnitsAddEquiv_H2_class, h2GalUnitsAddEquiv_H2_class, h2]
  rfl

end Bridge

section Restriction

variable (F F' Ω : Type) [Field F] [Field F'] [Field Ω] [Algebra F F'] [Algebra F' Ω] [Algebra F Ω]
  [IsScalarTower F F' Ω]

theorem continuous_restrictScalarsHom_of_tower :
    Continuous (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[F'] Ω) →* (Ω ≃ₐ[F] Ω)) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨S, hS, hSs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  let b := Module.finBasis F S
  let T : Set Ω := Set.range fun i => (b i : Ω)
  refine ⟨IntermediateField.adjoin F' T, ?_, ?_⟩
  · refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    exact ((IsIntegral.of_finite F (b i)).map S.val).tower_top
  · intro σ hσ
    apply hSs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    have hT : ∀ i, (AlgEquiv.restrictScalarsHom F σ) (b i : Ω) = b i := fun i =>
      hσ _ (IntermediateField.subset_adjoin F' T ⟨i, rfl⟩)
    have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ω) := by
      calc x = S.val (∑ i, b.repr ⟨x, hx⟩ i • b i) := by rw [b.sum_repr]; rfl
        _ = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ω) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => map_smul S.val _ _
    rw [hx', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT]

def galUnitsResScalars :
    Rep.res (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[F'] Ω) →* (Ω ≃ₐ[F] Ω)) (galUnits F Ω) ⟶
      galUnits F' Ω :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Ωˣ) (B := Additive Ωˣ) (AddMonoidHom.id _),
    fun σ => by
      ext x
      rfl⟩

@[simp]
theorem galUnitsResScalars_hom_apply (x : Additive Ωˣ) : (galUnitsResScalars F F' Ω).hom x = x :=
  rfl

variable [IsGalois F Ω] [IsGalois F' Ω]

noncomputable def brauerRes : galoisBrauerGroup F Ω ⟶ galoisBrauerGroup F' Ω :=
  cohomologyMapAlong (AlgEquiv.restrictScalarsHom F) (continuous_restrictScalarsHom_of_tower F F' Ω)
    (galUnitsResScalars F F' Ω) 2

theorem brauerRes_eq : brauerRes F F' Ω = cohomologyMapAlong (AlgEquiv.restrictScalarsHom F)
    (continuous_restrictScalarsHom_of_tower F F' Ω) (galUnitsResScalars F F' Ω) 2 :=
  rfl

end Restriction

section Square

variable (F F' Ω : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']
  [Algebra F F'] [ValuativeExtension F F'] [FiniteDimensional F F']
  [Field Ω] [Algebra F' Ω] [Algebra F Ω] [IsScalarTower F F' Ω] [IsSepClosure F Ω] [IsSepClosure F' Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]
  [ValuativeExtension F' Ω]

omit [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F'] [ValuativeExtension F F']
  [FiniteDimensional F F'] [ValuativeExtension F' Ω] in

theorem unitsInflationCochains_comp_cochainsMapAlong (E : IntermediateField F Ω)
    (E' : IntermediateField F' Ω) [FiniteDimensional F E] [Normal F E] [IsUnramified F E]
    [FiniteDimensional F' E'] [Normal F' E'] [Algebra E E'] [IsScalarTower F E E']
    (hι : ∀ x : E, ((algebraMap E E' x : E') : Ω) = x) :
    unitsInflationCochains E ≫ cochainsMapAlong (AlgEquiv.restrictScalarsHom F)
        (continuous_restrictScalarsHom_of_tower F F' Ω) (galUnitsResScalars F F' Ω) =
      groupCohomology.cochainsMap (galRestrict F F' E E') (unitsResHomU F F' E E') ≫
        unitsInflationCochains E' := by
  have hres : ∀ σ : Ω ≃ₐ[F'] Ω, AlgEquiv.restrictNormalHom E (AlgEquiv.restrictScalarsHom F σ) =
      galRestrict F F' E E' (AlgEquiv.restrictNormalHom E' σ) := by
    intro σ
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    calc ((AlgEquiv.restrictNormalHom E (AlgEquiv.restrictScalarsHom F σ) x : E) : Ω)
        = σ (x : Ω) := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalarsHom F σ) E x
      _ = σ ((algebraMap E E' x : E') : Ω) := by rw [hι]
      _ = ((AlgEquiv.restrictNormalHom E' σ (algebraMap E E' x) : E') : Ω) :=
          (AlgEquiv.restrictNormal_commutes σ E' _).symm
      _ = ((algebraMap E E' (galRestrict F F' E E' (AlgEquiv.restrictNormalHom E' σ) x) : E') : Ω) := by
          rw [algebraMap_galRestrict_apply]
      _ = _ := hι _
  ext n x : 3
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (galUnits F' Ω)).f n)).1 inferInstance
  funext g
  have hg : (fun i => AlgEquiv.restrictNormalHom E (AlgEquiv.restrictScalarsHom F (g i))) =
      ⇑(galRestrict F F' E E') ∘ fun i => AlgEquiv.restrictNormalHom E' (g i) :=
    funext fun i => hres (g i)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [cochainsComplexι_cochainsMapAlong_apply, unitsInflationCochains_f_hom_apply]
  beta_reduce
  erw [unitsInflationCochains_f_hom_apply]
  simp only [Function.comp_apply]
  rw [hg]
  apply Additive.toMul.injective
  apply Units.ext
  exact (hι _).symm

omit [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F'] [ValuativeExtension F F']
  [FiniteDimensional F F'] [ValuativeExtension F' Ω] in

theorem brauerRes_brauerInflation (E : IntermediateField F Ω)
    (E' : IntermediateField F' Ω) [FiniteDimensional F E] [Normal F E] [IsUnramified F E]
    [FiniteDimensional F' E'] [Normal F' E'] [Algebra E E'] [IsScalarTower F E E']
    (hι : ∀ x : E, ((algebraMap E E' x : E') : Ω) = x) (y : groupCohomology (galUnits F E) 2) :
    (brauerRes F F' Ω).hom ((brauerInflation E).hom y) =
      (brauerInflation E').hom ((unitsResH2Lift F F' E E').hom y) := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ 2)
    (unitsInflationCochains_comp_cochainsMapAlong F F' Ω E E' hι)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact congrArg (fun φ => φ.hom y) h

omit [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]
  [ValuativeExtension F' Ω] in

theorem unramifiedLevel_le_unramifiedLevel (n : ℕ+) :
    unramifiedLevel F Ω n ≤ (unramifiedLevel F' Ω n).restrictScalars F := by
  rw [unramifiedLevel_eq, adjoin_simple_le_iff, mem_restrictScalars]
  have hζ := isPrimitiveRoot_unramifiedRoot F Ω n
  have hζ' := isPrimitiveRoot_unramifiedRoot F' Ω n
  have hq := card_residueField_eq_pow_residueDegree F F'
  have hdvd : Nat.card 𝓀[F] ^ (n : ℕ) - 1 ∣ Nat.card 𝓀[F'] ^ (n : ℕ) - 1 := by
    rw [hq, ← pow_mul, mul_comm]
    exact pow_sub_one_dvd_pow_sub_one _ (dvd_mul_right _ _)
  have hpow : unramifiedRoot F Ω n ^ (Nat.card 𝓀[F'] ^ (n : ℕ) - 1) = 1 := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  have : NeZero (Nat.card 𝓀[F'] ^ (n : ℕ) - 1) := ⟨by
    have := Nat.one_lt_pow n.ne_zero (one_lt_card_residueField F')
    omega⟩
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hpow
  rw [unramifiedLevel_eq, ← hi]
  exact pow_mem (mem_adjoin_simple_self F' _) i

theorem brauerInv_brauerRes (x : galoisBrauerGroup F Ω) :
    brauerInv F' Ω ((brauerRes F F' Ω).hom x) = Module.finrank F F' • brauerInv F Ω x := by
  obtain ⟨n, y, rfl⟩ := exists_brauerInflation_unramifiedLevel F Ω x
  have hle := unramifiedLevel_le_unramifiedLevel F F' Ω n
  let ι : unramifiedLevel F Ω n →+* unramifiedLevel F' Ω n :=
    { toFun := fun a => ⟨a.1, hle a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra (unramifiedLevel F Ω n) (unramifiedLevel F' Ω n) := ι.toAlgebra
  have : IsScalarTower F (unramifiedLevel F Ω n) (unramifiedLevel F' Ω n) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      apply Subtype.ext
      change ((algebraMap F (unramifiedLevel F' Ω n) a : unramifiedLevel F' Ω n) : Ω) =
        algebraMap F Ω a
      rw [IsScalarTower.algebraMap_apply F F' (unramifiedLevel F' Ω n) a,
        IsScalarTower.algebraMap_apply F F' Ω a]
      rfl
  have : ValuativeExtension (unramifiedLevel F Ω n) (unramifiedLevel F' Ω n) :=
    ⟨fun a b => by
      rw [← IntermediateField.coe_vle_coe_iff (L := Ω) a b,
        ← IntermediateField.coe_vle_coe_iff (L := Ω)]
      rfl⟩
  rw [brauerRes_brauerInflation F F' Ω (unramifiedLevel F Ω n) (unramifiedLevel F' Ω n)
      (fun _ => rfl), brauerInv_brauerInflation,
    brauerInv_brauerInflation, unramifiedLevelInv_apply, unramifiedLevelInv_apply,
    h2GalUnitsAddEquiv_unitsResH2Lift, unramifiedInv_unitsResH2]

end Square

end GroundTheory.ProfCoh
