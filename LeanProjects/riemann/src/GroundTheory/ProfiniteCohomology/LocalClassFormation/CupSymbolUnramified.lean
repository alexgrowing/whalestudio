import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolDefs
import GroundTheory.ProfiniteCohomology.CyclicCupBrauer
import GroundTheory.ProfiniteCohomology.CyclicCup
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel groupCohomology
open GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

section Characters

variable {G : Type} [Group G] [Fintype G]

theorem h2IntAddEquiv_charClass (χ : Additive G →+ AddCircle (1 : ℚ)) :
    GroundTheory.GroupCoh.h2IntAddEquiv G (charClass χ) = χ :=
  (GroundTheory.GroupCoh.h2IntAddEquiv G).apply_symm_apply χ

end Characters

section UnramifiedInv

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsUnramified K L]

theorem unramifiedInv_cupCharClass (χ : Additive Gal(L/K) →+ AddCircle (1 : ℚ))
    (a : (galUnitsZ K L).ρ.invariants) :
    unramifiedInv K L ((cupCharClass (galUnitsZ K L) χ).hom a) =
      QZ.toAddCircle.symm (ord ((Additive.toMul (a : Additive Lˣ) : Lˣ) : L) •
        χ (Additive.ofMul (frob K L))) := by
  rw [unramifiedInv_apply, cupCharClass_apply_charCocycle]
  have hv : (h2Valuation K L).hom ((H2π (galUnitsZ K L)).hom ⟨fun p => charCocycle χ p • (a : galUnitsZ K L),
      smul_mem_cocycles₂ ⟨charCocycle χ, charCocycle_mem χ⟩ a⟩) =
      ord ((Additive.toMul (a : Additive Lˣ) : Lˣ) : L) • charClass χ := by
    rw [charClass_eq_H2π, ← map_zsmul, h2Valuation]
    erw [groupCohomology.H2π_comp_map_apply]
    congr 1
    refine Subtype.ext (funext fun p => ?_)
    change (unitsValuation K L).hom (charCocycle χ p • (a : galUnitsZ K L)) =
      ord ((Additive.toMul (a : Additive Lˣ) : Lˣ) : L) • charCocycle χ p
    rw [map_zsmul, unitsValuation_hom_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [hv, map_zsmul, h2IntAddEquiv_charClass]
  rfl

end UnramifiedInv

section Restrict

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

noncomputable def charRestrict (E : IntermediateField F Ω) [Normal F E]
    (ψ : Additive Gal(Ω/F) →ₜ+ QZ)
    (hE : ∀ g ∈ E.fixingSubgroup, ψ (Additive.ofMul g) = 0) :
    Additive Gal(E/F) →+ AddCircle (1 : ℚ) where
  toFun τ := charAdd ψ (Additive.ofMul ((Additive.toMul τ).liftNormal Ω))
  map_zero' := by
    have h : (AlgEquiv.liftNormal (1 : Gal(E/F)) Ω) ∈ E.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker]
      exact AlgEquiv.restrict_liftNormal _ _
    change QZ.toAddCircle (ψ (Additive.ofMul (AlgEquiv.liftNormal (1 : Gal(E/F)) Ω))) = 0
    rw [hE _ h, map_zero]
  map_add' τ₁ τ₂ := by
    have h : ((Additive.toMul τ₁).liftNormal Ω * (Additive.toMul τ₂).liftNormal Ω)⁻¹ *
        (Additive.toMul (τ₁ + τ₂)).liftNormal Ω ∈ E.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, map_mul]
      change ((AlgEquiv.liftNormal _ Ω).restrictNormal E * (AlgEquiv.liftNormal _ Ω).restrictNormal E)⁻¹ *
        (AlgEquiv.liftNormal _ Ω).restrictNormal E = 1
      rw [AlgEquiv.restrict_liftNormal, AlgEquiv.restrict_liftNormal, AlgEquiv.restrict_liftNormal]
      simp
    have e := hE _ h
    rw [ofMul_mul, map_add, ofMul_inv, map_neg, ofMul_mul, map_add] at e
    change QZ.toAddCircle (ψ _) = QZ.toAddCircle (ψ _) + QZ.toAddCircle (ψ _)
    rw [← map_add]
    exact congrArg QZ.toAddCircle (neg_add_eq_zero.1 e).symm

theorem charRestrict_apply (E : IntermediateField F Ω) [Normal F E]
    (ψ : Additive Gal(Ω/F) →ₜ+ QZ) (hE : ∀ g ∈ E.fixingSubgroup, ψ (Additive.ofMul g) = 0)
    (g : Gal(Ω/F)) :
    charRestrict E ψ hE (Additive.ofMul (AlgEquiv.restrictNormalHom E g)) = charAdd ψ (Additive.ofMul g) := by
  have h : g⁻¹ * (AlgEquiv.restrictNormalHom E g).liftNormal Ω ∈ E.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv]
    change (AlgEquiv.restrictNormalHom E g)⁻¹ *
      ((AlgEquiv.restrictNormalHom E g).liftNormal Ω).restrictNormal E = 1
    rw [AlgEquiv.restrict_liftNormal, inv_mul_cancel]
  have e := hE _ h
  rw [ofMul_mul, map_add, ofMul_inv, map_neg, neg_add_eq_zero] at e
  change QZ.toAddCircle (ψ (Additive.ofMul ((AlgEquiv.restrictNormalHom E g).liftNormal Ω))) = _
  rw [← e]
  rfl

end Restrict

section Field

variable {F Ω : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]

theorem restrictNormalHom_unramifiedLevel_eq_frob {σ : Gal(Ω/F)}
    (hσ : unramifiedDegree F Ω σ = Multiplicative.ofAdd 1) (n : ℕ+) :
    AlgEquiv.restrictNormalHom (unramifiedLevel F Ω n) σ = frob F (unramifiedLevel F Ω n) := by
  have hζ := isPrimitiveRoot_unramifiedRoot F Ω n
  have hpow : unramifiedRoot F Ω n ^ (Nat.card 𝓀[F] ^ (n : ℕ) - 1) = 1 := hζ.pow_eq_one
  have hmem : unramifiedRoot F Ω n ∈ unramifiedRoots F Ω := ⟨n, n.ne_zero, hpow⟩
  have h1 : σ (unramifiedRoot F Ω n) = unramifiedRoot F Ω n ^ Nat.card 𝓀[F] := by
    have := (unramifiedDegree_eq_ofAdd_natCast_iff σ 1).1 (by rw [Nat.cast_one]; exact hσ) _ hmem
    rwa [pow_one] at this
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin F
    (show unramifiedLevel F Ω n = IntermediateField.adjoin F {unramifiedRoot F Ω n} from
      unramifiedLevel_eq F Ω n) ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  apply Subtype.ext
  have hζE : (⟨unramifiedRoot F Ω n, mem_adjoin_simple_self F _⟩ : unramifiedLevel F Ω n) ^
      (Nat.card 𝓀[F] ^ (n : ℕ) - 1) = 1 := Subtype.ext hpow
  have h2 := frobenius_apply_of_pow_eq_one (K := F) (L := unramifiedLevel F Ω n)
    (IsUnramified.ramificationIndex_eq_one (K := F) (L := unramifiedLevel F Ω n))
    (natCast_card_pow_sub_one_ne_zero (K := F) n.ne_zero) hζE
  change ((AlgEquiv.restrictNormal σ (unramifiedLevel F Ω n)) ⟨_, _⟩ : Ω) =
    ((frob F (unramifiedLevel F Ω n)) ⟨_, _⟩ : Ω)
  rw [show ((frob F (unramifiedLevel F Ω n)) ⟨unramifiedRoot F Ω n, mem_adjoin_simple_self F _⟩ : Ω) =
    unramifiedRoot F Ω n ^ Nat.card 𝓀[F] from congrArg Subtype.val h2]
  rw [← h1]
  exact AlgEquiv.restrictNormal_commutes σ (unramifiedLevel F Ω n) _

variable (ψ : Additive Gal(Ω/F) →ₜ+ QZ)

noncomputable def charIndex : ℕ+ :=
  ⟨(charKer (charAdd ψ)).index, Nat.pos_of_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := ((charKerOpen ψ).toOpenSubgroup : Subgroup Gal(Ω/F))))⟩

omit [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω] in

theorem charAdd_eq_zero_of_mem_fixingSubgroup
    (hψ : ∀ g ∈ (unramifiedDegree F Ω).ker, ψ (Additive.ofMul g) = 0) :
    ∀ g ∈ (unramifiedLevel F Ω (charIndex ψ)).fixingSubgroup, ψ (Additive.ofMul g) = 0 := by
  intro g hg
  set n := charIndex ψ
  have hζ := isPrimitiveRoot_unramifiedRoot F Ω n
  have hfix : g (unramifiedRoot F Ω n) = unramifiedRoot F Ω n :=
    hg ⟨_, mem_adjoin_simple_self F (unramifiedRoot F Ω n)⟩
  have hc : ((0 : ℕ) : ZMod n) = unramifiedCoord F g n :=
    (natCast_eq_unramifiedCoord_iff hζ g 0).2 (by rw [pow_zero, pow_one]; exact hfix)
  have hp : proj n (Multiplicative.toAdd (unramifiedDegree F Ω g)) = 0 := by
    rw [proj_toAdd_unramifiedDegree, ← hc, Nat.cast_zero]
  obtain ⟨z, hz⟩ := mem_multiples.1 (proj_eq_zero_iff.1 hp)
  obtain ⟨h, hh⟩ := unramifiedDegree_surjective (K := F) (Ω := Ω) (Multiplicative.ofAdd z)
  have hk : (h ^ (n : ℕ))⁻¹ * g ∈ (unramifiedDegree F Ω).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hh]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, hz, toAdd_one, neg_add_cancel]
  have hn : h ^ (n : ℕ) ∈ charKer (charAdd ψ) := Subgroup.pow_index_mem _ h
  have e1 := hψ _ hk
  have e2 : ψ (Additive.ofMul (h ^ (n : ℕ))) = 0 := by
    have := mem_charKer.1 hn
    exact QZ.toAddCircle.injective (this.trans (map_zero _).symm)
  have : g = h ^ (n : ℕ) * ((h ^ (n : ℕ))⁻¹ * g) := by group
  rw [this, ofMul_mul, map_add, e1, e2, add_zero]

end Field

section Main

variable {F Ω : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω] in

theorem exists_cocycle_brauerInflation (E : IntermediateField F Ω) [FiniteDimensional F E] [Normal F E]
    (c : cocycles₂ (galUnits.{0} F E)) :
    ∃ z : cocycles (galUnits.{0} F Ω) 2,
      (brauerInflation E).hom ((H2π _).hom c) = cohomologyπ _ 2 z ∧
      ∀ v : Fin 2 → Gal(Ω/F), cochainOf _ (cocycleι _ 2 z) v =
        (unitsRestrictHom E).hom (c (AlgEquiv.restrictNormalHom E (v 0),
          AlgEquiv.restrictNormalHom E (v 1))) := by
  refine ⟨HomologicalComplex.cyclesMap (unitsInflationCochains E) 2 ((isoCocycles₂ _).inv c),
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (unitsInflationCochains E) 2) _,
    fun v => ?_⟩
  have e := congrArg (fun φ => φ.hom ((isoCocycles₂ _).inv c))
    (HomologicalComplex.cyclesMap_i (unitsInflationCochains E) 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  change ((cochainsComplexι (galUnits.{0} F Ω)).f 2).hom
    (((cochainsComplex (galUnits.{0} F Ω)).iCycles 2).hom _) v = _
  rw [e, unitsInflationCochains_f_hom_apply, isoCocycles₂_inv_comp_iCocycles_apply]
  rfl

theorem brauerInvZ_galCupClass_of_unramified (ψ : Additive Gal(Ω/F) →ₜ+ QZ)
    (hψ : ∀ g ∈ (unramifiedDegree F Ω).ker, ψ (Additive.ofMul g) = 0) {σ : Gal(Ω/F)}
    (hσ : unramifiedDegree F Ω σ = Multiplicative.ofAdd 1) (x : Fˣ) :
    brauerInvZ F Ω (galCupClass F Ω ψ x) = ord (x : F) • ψ (Additive.ofMul σ) := by
  have hE := charAdd_eq_zero_of_mem_fixingSubgroup ψ hψ
  let E := unramifiedLevel F Ω (charIndex ψ)
  let ψE := charRestrict E ψ hE
  let a := unitsInvariant F E x
  let w : cocycles₂ (galUnitsZ F E) := ⟨fun p => charCocycle ψE p • (a : galUnitsZ F E),
    smul_mem_cocycles₂ ⟨charCocycle ψE, charCocycle_mem ψE⟩ a⟩
  let c := (cocycles₂IntRepAddEquiv (galUnitsHom F E)).symm w
  obtain ⟨z, hz, hzc⟩ := exists_cocycle_brauerInflation E c
  obtain ⟨w', hw', hwc'⟩ := exists_cocycle_cupCharClassProf (galUnitsZ F Ω) ψ (unitsInvariant F Ω x)
  have hk : ∀ v : Fin 2 → Gal(Ω/F), charCocycle ψE (AlgEquiv.restrictNormalHom E (v 0),
      AlgEquiv.restrictNormalHom E (v 1)) = charCocycle (charAdd ψ) (v 0, v 1) := fun v => by
    simp only [charCocycle, ψE, charRestrict_apply]
  have ha : (unitsRestrictHom E).hom (a : galUnitsZ F E) = (unitsInvariant F Ω x : galUnitsZ F Ω) := by
    rfl
  have hbr : cohomologyULiftIntAddEquiv (galUnits.{0} F Ω) 2 (cohomologyπ _ 2 z) = galCupClass F Ω ψ x := by
    rw [galCupClass, ← hw']
    refine cohomologyULiftIntAddEquiv_cohomologyπ (galUnits.{0} F Ω) z w' (funext fun v => ?_)
    refine (hwc' v).trans ?_
    rw [hzc]
    change _ = (unitsRestrictHom E).hom (charCocycle ψE (AlgEquiv.restrictNormalHom E (v 0),
      AlgEquiv.restrictNormalHom E (v 1)) • (a : galUnitsZ F E))
    rw [hk, map_zsmul, ha]
  have h1 : h2GalUnitsAddEquiv F E ((H2π _).hom c) = (cupCharClass (galUnitsZ F E) ψE).hom a := by
    rw [h2GalUnitsAddEquiv_H2_class, cupCharClass_apply_charCocycle]
    rfl
  have hord : ord ((Additive.toMul (a : Additive Eˣ) : Eˣ) : E) = ord (x : F) := by
    change ord (algebraMap F E x) = _
    rw [ord_algebraMap, IsUnramified.ramificationIndex_eq_one (K := F) (L := E), Nat.cast_one, one_mul]
  rw [← hbr, brauerInvZ_cohomologyULiftIntAddEquiv, ← hz, brauerInv_brauerInflation,
    unramifiedLevelInv_apply, h1, unramifiedInv_cupCharClass, hord,
    ← restrictNormalHom_unramifiedLevel_eq_frob hσ, charRestrict_apply]
  change QZ.toAddCircle.symm (ord (x : F) • QZ.toAddCircle (ψ (Additive.ofMul σ))) = _
  rw [← map_zsmul, AddEquiv.symm_apply_apply]

end Main

end GroundTheory.ProfCoh
