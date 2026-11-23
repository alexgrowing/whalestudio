import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderBound
import GroundTheory.TateCohomology.InfRes
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits

universe u

section Tower

theorem additive_units_ext {M : Type u} [Field M] {x y : Additive Mˣ}
    (h : ((Additive.toMul x : Mˣ) : M) = ((Additive.toMul y : Mˣ) : M)) : x = y :=
  Additive.toMul.injective (Units.ext h)

variable (K F M : Type u) [Field K] [Field F] [Field M] [Algebra K F] [Algebra K M] [Algebra F M]
  [IsScalarTower K F M]

def galRestrictScalars : Gal(M/F) →* Gal(M/K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem galRestrictScalars_apply (σ : Gal(M/F)) (x : M) : galRestrictScalars K F M σ x = σ x :=
  rfl

theorem galRestrictScalars_injective : Function.Injective (galRestrictScalars K F M) :=
  fun _ _ h => AlgEquiv.ext fun x => DFunLike.congr_fun h x

def unitsResScalarsHom :
    Rep.res (galRestrictScalars K F M) (galUnits.{u} K M) ⟶ galUnits.{u} F M :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

noncomputable def unitsRes (n : ℕ) :
    groupCohomology (galUnits.{u} K M) n ⟶ groupCohomology (galUnits.{u} F M) n :=
  groupCohomology.map (galRestrictScalars K F M) (unitsResScalarsHom K F M) n

variable [Normal K F]

noncomputable def unitsInclHom :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) F) (galUnits.{u} K F) ⟶
      galUnits.{u} K M :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Fˣ) (B := Additive Mˣ)
    (MonoidHom.toAdditive (Units.map ((algebraMap F M : F →+* M) : F →* M))), fun σ => by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ F ((Additive.toMul (α := Fˣ) x : Fˣ) : F)⟩

noncomputable def unitsInfl (n : ℕ) :
    groupCohomology (galUnits.{u} K F) n ⟶ groupCohomology (galUnits.{u} K M) n :=
  groupCohomology.map (AlgEquiv.restrictNormalHom F) (unitsInclHom K F M) n

variable [FiniteDimensional K M] [IsGalois K M]

noncomputable abbrev galFixing : Subgroup Gal(M/K) :=
  (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) F).ker

omit [FiniteDimensional K M] [IsGalois K M] in
theorem mem_galFixing_iff (σ : Gal(M/K)) :
    σ ∈ galFixing K F M ↔ ∀ x : F, σ (algebraMap F M x) = algebraMap F M x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x
    rw [← AlgEquiv.restrictNormal_commutes σ F x]
    change algebraMap F M ((AlgEquiv.restrictNormalHom F σ) x) = _
    rw [h]
    rfl
  · intro h
    ext x
    apply (algebraMap F M).injective
    change algebraMap F M ((AlgEquiv.restrictNormal σ F) x) = _
    rw [AlgEquiv.restrictNormal_commutes, h]
    rfl

omit [FiniteDimensional K M] [IsGalois K M] in
theorem range_galRestrictScalars : (galRestrictScalars K F M).range = galFixing K F M := by
  ext σ
  rw [mem_galFixing_iff]
  constructor
  · rintro ⟨τ, rfl⟩ x
    exact τ.commutes x
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) h, AlgEquiv.ext fun _ => rfl⟩

noncomputable def galFixingEquiv : Gal(M/F) ≃* galFixing K F M :=
  (MonoidHom.ofInjective (galRestrictScalars_injective K F M)).trans
    (MulEquiv.subgroupCongr (range_galRestrictScalars K F M))

omit [FiniteDimensional K M] [IsGalois K M] in
@[simp]
theorem coe_galFixingEquiv_apply (σ : Gal(M/F)) (x : M) :
    (galFixingEquiv K F M σ : Gal(M/K)) x = σ x :=
  rfl

noncomputable def galFixingCohomologyIso (n : ℕ) :
    groupCohomology (galUnits.{u} F M) n ≅
      groupCohomology (Rep.res (galFixing K F M).subtype (galUnits.{u} K M)) n :=
  groupCohomology.mapIso (galFixingEquiv K F M) (LinearEquiv.refl _ _)
    (fun _ => LinearMap.ext fun _ => rfl) n

omit [FiniteDimensional K M] [IsGalois K M] in
theorem unitsRes_eq (n : ℕ) :
    unitsRes K F M n = GroundTheory.GroupCoh.restriction (galUnits.{u} K M) (galFixing K F M) n ≫
      (galFixingCohomologyIso K F M n).inv := by
  have hinv : (galFixingCohomologyIso K F M n).inv = groupCohomology.map
      (galFixingEquiv K F M : Gal(M/F) →* galFixing K F M)
      (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩ : Rep.res (galFixingEquiv K F M : Gal(M/F) →* _)
        (Rep.res (galFixing K F M).subtype (galUnits.{u} K M)) ⟶ galUnits.{u} F M) n := rfl
  rw [hinv, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ n
  · ext σ x
    rfl
  · rfl

omit [IsGalois K M] in
theorem isZero_groupCohomology_one_galFixing :
    IsZero (groupCohomology (Rep.res (galFixing K F M).subtype (galUnits.{u} K M)) 1) := by
  have : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite K F M
  exact (isZero_groupCohomology_one_galUnits F M).of_iso (galFixingCohomologyIso K F M 1).symm

noncomputable def unitsToInvariantsTower :
    Additive Fˣ →ₗ[ULift.{u} ℤ]
      Representation.invariants ((galUnits.{u} K M).ρ.comp (galFixing K F M).subtype) :=
  LinearMap.codRestrict _ (unitsInclHom K F M).hom.toLinearMap fun x σ => by
    apply Additive.toMul.injective
    apply Units.ext
    exact (mem_galFixing_iff K F M σ.1).1 σ.2 _

theorem unitsToInvariantsTower_bijective : Function.Bijective (unitsToInvariantsTower K F M) := by
  have : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite K F M
  have : IsGalois F M := IsGalois.tower_top_of_isGalois K F M
  constructor
  · intro x y h
    have h' := congrArg (fun v => ((Additive.toMul (α := Mˣ) v.1 : Mˣ) : M)) h
    apply Additive.toMul.injective
    apply Units.ext
    exact (algebraMap F M).injective h'
  · intro v
    have hfix : ∀ τ : Gal(M/F), τ ((Additive.toMul (α := Mˣ) v.1 : Mˣ) : M) =
        ((Additive.toMul (α := Mˣ) v.1 : Mˣ) : M) := by
      intro τ
      have := v.2 ⟨galRestrictScalars K F M τ, (range_galRestrictScalars K F M) ▸ ⟨τ, rfl⟩⟩
      exact congrArg (fun w => ((Additive.toMul (α := Mˣ) w : Mˣ) : M)) this
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed _).2 hfix)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (Additive.toMul (α := Mˣ) v.1).ne_zero hy.symm
    refine ⟨Additive.ofMul (Units.mk0 y hy0), Subtype.ext ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    exact hy

noncomputable def unitsInvariantsEquivTower :
    Additive Fˣ ≃ₗ[ULift.{u} ℤ]
      Representation.invariants ((galUnits.{u} K M).ρ.comp (galFixing K F M).subtype) :=
  LinearEquiv.ofBijective _ (unitsToInvariantsTower_bijective K F M)

noncomputable def galQuotientEquiv : Gal(M/K) ⧸ galFixing K F M ≃* Gal(F/K) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (AlgEquiv.restrictNormalHom_surjective M)

noncomputable def galQuotientCohomologyIso (n : ℕ) :
    groupCohomology (galUnits.{u} K F) n ≅
      groupCohomology ((galUnits.{u} K M).quotientToInvariants (galFixing K F M)) n :=
  groupCohomology.mapIso (galQuotientEquiv K F M).symm (unitsInvariantsEquivTower K F M) (fun g => by
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) M g
    have hq : (galQuotientEquiv K F M).symm (AlgEquiv.restrictNormalHom F σ) =
        (σ : Gal(M/K) ⧸ galFixing K F M) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hq]
    refine LinearMap.ext fun x => Subtype.ext (additive_units_ext ?_)
    exact AlgEquiv.restrictNormal_commutes σ F ((Additive.toMul (α := Fˣ) x : Fˣ) : F)) n

theorem unitsInfl_eq (n : ℕ) :
    unitsInfl K F M n = (galQuotientCohomologyIso K F M n).hom ≫
      GroundTheory.GroupCoh.inflation (galUnits.{u} K M) (galFixing K F M) n := by
  have hhom : (galQuotientCohomologyIso K F M n).hom = groupCohomology.map
      (galQuotientEquiv K F M : Gal(M/K) ⧸ galFixing K F M →* Gal(F/K))
      (Rep.ofHom ⟨(unitsInvariantsEquivTower K F M).toLinearMap, fun g => by
        obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
        refine LinearMap.ext fun x => Subtype.ext (additive_units_ext ?_)
        exact AlgEquiv.restrictNormal_commutes σ F ((Additive.toMul (α := Fˣ) x : Fˣ) : F)⟩ :
        Rep.res (galQuotientEquiv K F M : Gal(M/K) ⧸ galFixing K F M →* Gal(F/K))
          (galUnits.{u} K F) ⟶ (galUnits.{u} K M).quotientToInvariants (galFixing K F M)) n := rfl
  rw [hhom, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ n
  · ext σ x
    rfl
  · rfl

theorem unitsInfl_two_injective : Function.Injective (unitsInfl K F M 2).hom := by
  rw [unitsInfl_eq, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact (GroundTheory.GroupCoh.inflation_two_injective (A := galUnits.{u} K M) (S := galFixing K F M)
    (isZero_groupCohomology_one_galFixing K F M)).comp
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

theorem range_unitsInfl_two_eq_ker_unitsRes :
    LinearMap.range (unitsInfl K F M 2).hom = LinearMap.ker (unitsRes K F M 2).hom := by
  have hsurj : Function.Surjective (galQuotientCohomologyIso K F M 2).hom.hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hinj : Function.Injective (galFixingCohomologyIso K F M 2).inv.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  rw [unitsInfl_eq, unitsRes_eq, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.2 hsurj, Submodule.map_top, LinearMap.ker_comp,
    LinearMap.ker_eq_bot.2 hinj, Submodule.comap_bot]
  exact GroundTheory.GroupCoh.range_inflation_two_eq_ker_restriction (A := galUnits.{u} K M)
    (S := galFixing K F M) (isZero_groupCohomology_one_galFixing K F M)

end Tower

section Count

variable (K E F M : Type u) [Field K] [Field E] [Field F] [Field M] [Algebra K E] [Algebra K F]
  [Algebra K M] [Algebra E M] [Algebra F M] [IsScalarTower K E M] [IsScalarTower K F M]
  [Normal K E] [Normal K F] [FiniteDimensional K M] [IsGalois K M]

theorem natCard_le_of_unitsInfl_comp_unitsRes_eq_zero
    (h : unitsInfl K E M 2 ≫ unitsRes K F M 2 = 0)
    [Finite (groupCohomology (galUnits.{u} K F) 2)] :
    Nat.card (groupCohomology (galUnits.{u} K E) 2) ≤
      Nat.card (groupCohomology (galUnits.{u} K F) 2) := by
  have hmem : ∀ y, (unitsInfl K E M 2).hom y ∈ LinearMap.range (unitsInfl K F M 2).hom := by
    intro y
    rw [range_unitsInfl_two_eq_ker_unitsRes, LinearMap.mem_ker]
    exact congrArg (fun φ => φ.hom y) h
  choose g hg using hmem
  refine Nat.card_le_card_of_injective g fun y y' hyy' => ?_
  apply unitsInfl_two_injective K E M
  rw [← hg y, ← hg y', hyy']

end Count

end GroundTheory.ProfCoh
