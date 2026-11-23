import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolUnramified
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolNorm
import GroundTheory.LocalFields.LocalArtinBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel
open GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

section Top

variable (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

theorem brauerInvZ_eq_inv_top (x : cohomology (galUnitsZ K Ω) 2) :
    brauerInvZ K Ω x = (localClassFormationZ K Ω).inv ⊤
      ((cohomologyRes (galUnitsZ K Ω) ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) 2).hom x) := by
  obtain ⟨y, rfl⟩ := (cohomologyULiftIntAddEquiv (galUnits.{0} K Ω) 2).surjective x
  rw [brauerInvZ_cohomologyULiftIntAddEquiv, localClassFormationZ_inv]
  have e := cohomologyULiftIntAddEquiv_cohomologyMapAlong (galUnits.{0} K Ω)
    (((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))).subtype (continuous_subgroup_subtype _)
    (𝟙 (Rep.res (((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))).subtype (galUnits.{0} K Ω)))
    (𝟙 (Rep.res (((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))).subtype (galUnitsZ K Ω)))
    (fun _ => rfl) 2 y
  refine Eq.trans ?_ (congrArg (localInv K Ω ⊤)
    ((congrArg (cohomologyULiftIntAddEquiv (Rep.res (((⊤ : OpenSubgroup Gal(Ω/K)) :
      Subgroup Gal(Ω/K))).subtype (galUnits.{0} K Ω)) 2).symm e.symm).trans
      (AddEquiv.symm_apply_apply _ _))).symm
  rw [localInv_apply]
  have : IsSepClosure (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω :=
    ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K _ Ω⟩
  have : IsGalois (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω :=
    IsGalois.tower_top_of_isGalois K _ Ω
  have hres : (openCohomologyIso (⊤ : OpenSubgroup Gal(Ω/K)) 2).hom.hom
      ((cohomologyMapAlong (((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))).subtype
        (continuous_subgroup_subtype _) (𝟙 _) 2).hom y) =
      (brauerRes K (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω).hom y := by
    rw [openCohomologyIso_hom, ← ModuleCat.comp_apply, ← cohomologyMapAlong_comp, brauerRes_eq]
    congr 1
  have hrank : Module.finrank K (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) = 1 := by
    rw [← index_openSubgroup]
    exact Subgroup.index_top
  rw [hres, brauerInv_brauerRes, hrank, one_smul]

end Top

section Subgroups

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [IsSepClosure K Ω] in

instance isDiscreteRep_res_galUnitsZ (S : Subgroup Gal(Ω/K)) :
    IsDiscreteRep (Rep.res S.subtype (galUnitsZ K Ω)) :=
  isDiscreteRep_res_subtype _ _

def fixedToInvariants (H : Subgroup Gal(Ω/K)) (u : Abstract.fixedModule Ωˣ H) :
    (Rep.res H.subtype (galUnitsZ K Ω)).ρ.invariants :=
  ⟨Additive.ofMul (u : Ωˣ), fun h => by
    apply Additive.toMul.injective
    apply Units.ext
    exact (coe_galUnitsHom_apply K Ω (h : Gal(Ω/K)) _).trans
      ((mem_fixedModule_units_iff' H (u : Ωˣ)).1 u.2 h h.2)⟩

omit [IsSepClosure K Ω] in
theorem fixedToInvariants_mul (H : Subgroup Gal(Ω/K)) (u v : Abstract.fixedModule Ωˣ H) :
    fixedToInvariants H (u * v) = fixedToInvariants H u + fixedToInvariants H v :=
  rfl

theorem fixedToInvariants_norm (S : OpenSubgroup Gal(Ω/K)) (x : Abstract.fixedModule Ωˣ (S : Subgroup Gal(Ω/K))) :
    fixedToInvariants ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))
        (Abstract.norm Ωˣ ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) (S : Subgroup Gal(Ω/K)) x) =
      invariantsNormLE (galUnitsZ K Ω) (le_top : S ≤ ⊤) (fixedToInvariants (S : Subgroup Gal(Ω/K)) x) := by
  classical
  apply Subtype.ext
  rw [coe_invariantsNormLE]
  change Additive.ofMul (Abstract.normFun Ωˣ _ _ x) = _
  let _ := Fintype.ofFinite (((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) ⧸
    (S : Subgroup Gal(Ω/K)).subgroupOf ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)))
  rw [Abstract.normFun, finprod_eq_prod_of_fintype, ofMul_prod]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_lhs => rw [← QuotientGroup.out_eq' c]
  rw [Abstract.cosetSMul_mk]
  apply Additive.toMul.injective
  apply Units.ext
  exact (coe_galUnitsHom_apply K Ω _ _).symm

end Subgroups

section Transport

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

theorem ord_eq_of_eq {E₁ E₂ : IntermediateField K Ω} [FiniteDimensional K E₁] [FiniteDimensional K E₂]
    (h : E₁ = E₂) (y : Ω) (h₁ : y ∈ E₁) (h₂ : y ∈ E₂) :
    ord (⟨y, h₁⟩ : E₁) = ord (⟨y, h₂⟩ : E₂) := by
  subst h
  rfl

theorem unramifiedDegree_eq_of_eq {E₁ E₂ : IntermediateField K Ω} [FiniteDimensional K E₁]
    [FiniteDimensional K E₂] (h : E₁ = E₂) (g₁ : Gal(Ω/E₁)) (g₂ : Gal(Ω/E₂)) (hg : ∀ y, g₁ y = g₂ y) :
    unramifiedDegree E₁ Ω g₁ = unramifiedDegree E₂ Ω g₂ := by
  subst h
  congr 1
  exact AlgEquiv.ext hg

end Transport

section OpenSubgroup

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

noncomputable def galUnitsZOpenHom (U : OpenSubgroup Gal(Ω/K)) :
    Rep.res (galFixedFieldEquivOpen U).toMonoidHom
        (Rep.res (U : Subgroup Gal(Ω/K)).subtype (galUnitsZ K Ω)) ⟶
      galUnitsZ (fixedField (U : Subgroup Gal(Ω/K))) Ω :=
  Rep.ofHom ⟨(AddMonoidHom.id (Additive Ωˣ)).toIntLinearMap, fun σ => by
    ext x
    rfl⟩

theorem galFixedFieldEquivOpen_symm_apply (U : OpenSubgroup Gal(Ω/K)) (σ : (U : Subgroup Gal(Ω/K)))
    (x : Ω) : ((galFixedFieldEquivOpen U).symm σ) x = (σ : Gal(Ω/K)) x := by
  conv_rhs => rw [← (galFixedFieldEquivOpen U).apply_symm_apply σ]
  rfl

end OpenSubgroup

section Prime

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

theorem localClassFormationZ_inv_cupCharClassProf_of_prime (E : IntermediateField K Ω)
    [FiniteDimensional K E] (χ : Additive Gal(Ω/K) →ₜ+ QZ)
    (π : Abstract.fixedModule Ωˣ ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)))
    (hπ : (localClassFieldData K Ω).valuation (fixingOpenSubgroup E) π = Multiplicative.ofAdd 1)
    (σ : ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)))
    (hσ : (localClassFieldData K Ω).relDeg (fixingOpenSubgroup E) σ = Multiplicative.ofAdd 1)
    (hχ : ∀ g ∈ ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) ⊓
      (localClassFieldData K Ω).deg.ker, χ (Additive.ofMul g) = 0) :
    (localClassFormationZ K Ω).inv (fixingOpenSubgroup E)
      ((cupCharClassProf (Rep.res ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) :
          Subgroup Gal(Ω/K)).subtype (galUnitsZ K Ω))
        (contCharComp χ _ (continuous_subgroup_subtype _))).hom
          (fixedToInvariants _ π)) = χ (Additive.ofMul (σ : Gal(Ω/K))) := by
  have hSig : fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) = E := by
    rw [coe_fixingOpenSubgroup]
    exact InfiniteGalois.fixedField_fixingSubgroup E
  have hπmem : ((π : Ωˣ) : Ω) ∈
      fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) :=
    (mem_fixedField_iff _ _).2 fun g hg => (mem_fixedModule_units_iff' _ _).1 π.2 g hg
  let π' : (fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)))ˣ :=
    Units.mk0 ⟨_, hπmem⟩ (fun h => (π : Ωˣ).ne_zero (congrArg Subtype.val h))
  let χS : Additive Gal(Ω/fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) :
      Subgroup Gal(Ω/K))) →ₜ+ QZ :=
    contCharComp χ (AlgEquiv.restrictScalarsHom K) (continuous_restrictScalarsHom_of_tower _ _ _)
  let σ' := (galFixedFieldEquivOpen (fixingOpenSubgroup E)).symm σ

  have hcup : (cohomologyMapAlong (galFixedFieldEquivOpen (fixingOpenSubgroup E)).toMonoidHom
      (continuous_galFixedFieldEquivOpen _) (galUnitsZOpenHom (fixingOpenSubgroup E)) 2).hom
      ((cupCharClassProf (Rep.res ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) :
          Subgroup Gal(Ω/K)).subtype (galUnitsZ K Ω))
        (contCharComp χ _ (continuous_subgroup_subtype _))).hom (fixedToInvariants _ π)) =
      galCupClass _ Ω χS π' := by
    have hab : ((unitsInvariant _ Ω π' : (galUnitsZ _ Ω).ρ.invariants) : galUnitsZ _ Ω) =
        (galUnitsZOpenHom (fixingOpenSubgroup E)).hom (fixedToInvariants _ π : _) := by
      apply Additive.toMul.injective
      apply Units.ext
      rfl
    rw [cohomologyMapAlong_cupCharClassProf _ _ _ _ _ (unitsInvariant _ Ω π') hab]
    rfl
  have e := cohomologyULiftIntAddEquiv_cohomologyMapAlong
    (Rep.res ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)).subtype
      (galUnits.{0} K Ω))
    (galFixedFieldEquivOpen (fixingOpenSubgroup E)).toMonoidHom (continuous_galFixedFieldEquivOpen _)
    (galUnitsOpenHom (fixingOpenSubgroup E)) (galUnitsZOpenHom (fixingOpenSubgroup E))
    (fun _ => rfl) 2
  rw [localClassFormationZ_inv, localInv_apply, openCohomologyIso_hom,
    ← brauerInvZ_cohomologyULiftIntAddEquiv]
  refine (congrArg (brauerInvZ _ Ω) ((e _).trans ((congrArg _ (AddEquiv.apply_symm_apply _ _)).trans
    hcup))).trans ?_

  have hord : ord ((π' : fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) :
      Subgroup Gal(Ω/K)))) = 1 := by
    have h := valuation_fixingOpenSubgroup E π
    rw [hπ] at h
    have h' : ((ord ((unitsEquivFixingOpen K E π : Eˣ) : E) : ℤ) : ℤ̂) = ((1 : ℤ) : ℤ̂) := by
      rw [Int.cast_one]
      exact (Multiplicative.ofAdd.injective h).symm
    rw [← Int.cast_injective h']
    exact ord_eq_of_eq hSig _ _ _
  have hσ' : unramifiedDegree _ Ω σ' = Multiplicative.ofAdd 1 := by
    rw [← hσ, relDeg_fixingOpenSubgroup E σ]
    exact unramifiedDegree_eq_of_eq hSig _ _ (fun y => galFixedFieldEquivOpen_symm_apply _ σ y)
  have hψ : ∀ g ∈ (unramifiedDegree (fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) :
      Subgroup Gal(Ω/K))) Ω).ker, χS (Additive.ofMul g) = 0 := by
    intro g hg
    set g₀ := galFixedFieldEquivOpen (fixingOpenSubgroup E) g
    have h1 : (localClassFieldData K Ω).relDeg (fixingOpenSubgroup E) g₀ = 1 := by
      rw [relDeg_fixingOpenSubgroup E g₀]
      refine (unramifiedDegree_eq_of_eq hSig.symm _ g (fun y => rfl)).trans hg
    rw [ClassFieldData.relDeg_eq_iff, one_pow] at h1
    exact hχ (g₀ : Gal(Ω/K)) ⟨g₀.2, h1⟩
  rw [brauerInvZ_galCupClass_of_unramified χS hψ hσ' π', hord, one_smul]
  change χ (Additive.ofMul (AlgEquiv.restrictScalarsHom K σ')) = _
  congr 2
  exact AlgEquiv.ext fun y => galFixedFieldEquivOpen_symm_apply _ σ y

end Prime

end GroundTheory.ProfCoh
