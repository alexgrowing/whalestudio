import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerLocalDefs
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalRestriction
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Splitting
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SumInvariants
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.CupDecompositionGlobal
import GroundTheory.ProfiniteCohomology.InflationRestriction
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplitLayers
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section TowerInfl

variable {k L : Type} [Field k] [Field L] [Algebra k L] [IsGalois k L] (M : IntermediateField k L)
  [Normal k M]

theorem cohomologyMapAlong_restrictNormalHom_two_injective :
    Function.Injective (cohomologyMapAlong (AlgEquiv.restrictNormalHom M)
      (InfiniteGalois.restrictNormalHom_continuous M) (unitsRestrictHom M) 2).hom := by
  have : Algebra.IsSeparable k M := Algebra.isSeparable_tower_bot_of_isSeparable k M L
  have : IsGalois k M := ⟨⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨E, y, rfl⟩ := exists_unitsInflation_eq (K := k) (L := M) 2 x
  let E₀ : IntermediateField k M := E.toIntermediateField
  let E' : IntermediateField k L := E₀.map M.val
  let e : E₀ ≃ₐ[k] E' := E₀.equivMap M.val
  let _ : Algebra E₀ E' := e.toRingHom.toAlgebra
  have : IsScalarTower k E₀ E' := IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  have : FiniteDimensional k E' := e.toLinearEquiv.finiteDimensional
  have : Normal k E' := Normal.of_algEquiv e
  have : Algebra.IsSeparable k E' := Algebra.isSeparable_tower_bot_of_isSeparable k E' L
  have : IsGalois k E' := ⟨⟩
  have hg : ∀ σ : Gal(L/k), AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom M σ) =
      AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom E' σ) := by
    intro σ
    have hE : ∀ z : E₀, ((algebraMap E₀ E' z : E') : L) = ((z : M) : L) := fun z => rfl
    apply AlgEquiv.ext
    intro a
    apply Subtype.val_injective
    apply Subtype.val_injective
    have l1 := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormalHom M σ) E₀ a
    have l2 := AlgEquiv.restrictNormal_commutes σ M (a : M)
    have r1 := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormalHom E' σ) E₀ a
    have r2 := AlgEquiv.restrictNormal_commutes σ E' (algebraMap E₀ E' a)
    calc (((AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom M σ) a : E₀) : M) : L)
        = ((AlgEquiv.restrictNormalHom M σ (a : M) : M) : L) := congrArg Subtype.val l1
      _ = σ ((a : M) : L) := l2
      _ = σ ((algebraMap E₀ E' a : E') : L) := by rw [hE]
      _ = ((AlgEquiv.restrictNormalHom E' σ (algebraMap E₀ E' a) : E') : L) := r2.symm
      _ = ((algebraMap E₀ E' (AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom E' σ) a) : E') :
          L) := congrArg Subtype.val r1.symm
      _ = _ := hE _
  have key : unitsInflation E₀ 2 ≫ cohomologyMapAlong (AlgEquiv.restrictNormalHom M)
      (InfiniteGalois.restrictNormalHom_continuous M) (unitsRestrictHom M) 2 =
      unitsInflationTower k E₀ E' 2 ≫ unitsInflation E' 2 := by
    unfold unitsInflation unitsInflationTower groupCohomology.map cohomologyMapAlong
    erw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    ext n : 1
    rw [← cancel_mono ((cochainsComplexι (galUnits k L)).f n), HomologicalComplex.comp_f,
      HomologicalComplex.comp_f, Category.assoc, Category.assoc]
    ext c : 2
    funext g
    change (unitsRestrictHom M).hom ((unitsRestrictHom E₀).hom
        (c fun i => AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom M (g i)))) =
      (unitsRestrictHom E').hom ((unitsTowerHom k E₀ E').hom
        (c fun i => AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom E' (g i))))
    simp only [hg]
    exact Additive.toMul.injective (Units.ext rfl)
  have h1 : (unitsInflation E' 2).hom ((unitsInflationTower k E₀ E' 2).hom y) = 0 := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← key, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact hx
  have h2 := brauerInflation_injective E' (h1.trans (map_zero _).symm)
  have h3 := unitsInflationTower_two_injective k E₀ E' (h2.trans (map_zero _).symm)
  rw [h3, map_zero]

end TowerInfl

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

instance isDiscreteRep_uliftIntToIntRep_galUnits_algebraicClosure :
    IsDiscreteRep (uliftIntToIntRep (galUnits K.1 ℚ̄)) :=
  isDiscreteRep_uliftIntToIntRep _

def galToFixing : Gal(ℚ̄/K.1) →* K.1.fixingSubgroup :=
  (IntermediateField.fixingSubgroupEquiv K.1).symm.toMonoidHom

theorem continuous_galToFixing : Continuous (galToFixing K) :=
  continuous_induced_rng.2 (continuous_restrictScalarsHom_of_tower ℚ K.1 ℚ̄)

def galToFixingUnitsMor :
    Rep.res (galToFixing K) (unitsLimitRep K) ⟶ uliftIntToIntRep (galUnits K.1 ℚ̄) :=
  Rep.ofHom ⟨(AddMonoidHom.id (Additive ℚ̄ˣ)).toIntLinearMap, fun _ => rfl⟩

def maxUnitsRestrictMor :
    Rep.res (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S))
        (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))) ⟶
      uliftIntToIntRep (galUnits K.1 ℚ̄) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive
      (Units.map (maxUnramifiedOutside K.1 ℚ̄ S).val.toRingHom.toMonoidHom)).toIntLinearMap,
    fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext
      (AlgEquiv.restrictNormal_commutes σ (maxUnramifiedOutside K.1 ℚ̄ S)
        ((Additive.toMul (α := (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) x :
          (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S)))⟩

theorem gsRestrict_comp_galToFixing :
    (gsRestrict K S).comp (galToFixing K) =
      AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S) := by
  refine MonoidHom.ext fun σ => AlgEquiv.ext fun y => Subtype.ext ?_
  exact (gsRestrict_apply K S (galToFixing K σ) y).trans
    (AlgEquiv.restrictNormal_commutes σ (maxUnramifiedOutside K.1 ℚ̄ S) y).symm

set_option maxHeartbeats 1000000 in

theorem gsBrauerInfl_injective : Function.Injective (gsBrauerInfl K S 2).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x', rfl⟩ :=
    (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).surjective x
  suffices h : (cohomologyMapAlong (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S))
      (InfiniteGalois.restrictNormalHom_continuous _)
      (unitsRestrictHom (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom x' = 0 by
    rw [cohomologyMapAlong_restrictNormalHom_two_injective _ (h.trans (map_zero _).symm), map_zero]
  apply (cohomologyULiftIntAddEquiv (galUnits K.1 ℚ̄) 2).injective
  rw [map_zero, cohomologyULiftIntAddEquiv_cohomologyMapAlong (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))
    (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S))
    (InfiniteGalois.restrictNormalHom_continuous _) (unitsRestrictHom (maxUnramifiedOutside K.1 ℚ̄ S))
    (maxUnitsRestrictMor K S) (fun _ => rfl) 2 x']
  have e : cohomologyMapAlong (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S))
      (InfiniteGalois.restrictNormalHom_continuous _) (maxUnitsRestrictMor K S) 2 =
      gsBrauerInfl K S 2 ≫ cohomologyMapAlong (galToFixing K) (continuous_galToFixing K)
        (galToFixingUnitsMor K) 2 := by
    rw [gsBrauerInfl, ← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_congr _ _ _ _ (gsRestrict_comp_galToFixing K S).symm (fun _ => rfl) 2
  rw [e, ConcreteCategory.comp_apply, hx, map_zero]

section Local

variable {v : HeightOneSpectrum (𝓞 K.1)} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

theorem gsRestrict_comp_globalDecomp :
    (gsRestrict K S).comp (globalDecomp (v.adicCompletion K.1) ι) =
      decompHomS (v.adicCompletion K.1) S ι := by
  refine MonoidHom.ext fun σ => ((decompHom_eq_iff _ σ _).2 fun y => ?_).symm
  change ι (((gsRestrict K S (globalDecomp (v.adicCompletion K.1) ι σ) y :
    maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) = σ (ι (y : ℚ̄))
  rw [gsRestrict_apply]
  exact globalDecomp_apply _ ι σ y

theorem gsUnitsMor_comp_unitsLocalMor_hom_apply (a : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    ((Rep.resFunctor (globalDecomp (v.adicCompletion K.1) ι)).map (gsUnitsMor K S) ≫
      unitsLocalMor (v.adicCompletion K.1) ι).hom a = (embUnitsMorZ S ι).hom a :=
  Additive.toMul.injective (Units.ext rfl)

theorem gsBrauerInfl_comp_unitsLocalRes (n : ℕ) :
    gsBrauerInfl K S n ≫ unitsLocalRes (v.adicCompletion K.1) ι n = gsLocalRes S ι n := by
  rw [gsBrauerInfl, unitsLocalRes, ← cohomologyMapAlong_comp, gsLocalRes]
  exact cohomologyMapAlong_congr _ _ _ _ (gsRestrict_comp_globalDecomp K S ι)
    (gsUnitsMor_comp_unitsLocalMor_hom_apply K S ι) n

end Local

set_option maxHeartbeats 2000000 in

theorem brauerLocal_gsBrauerInfl_inr (ιs : LocalEmbeddings K) (v : HeightOneSpectrum (𝓞 K.1))
    (x : cohomology (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))) 2) :
    brauerLocal ιs ((gsBrauerInfl K S 2).hom x) (.inr v) = (gsLocalRes S (ιs.fin v) 2).hom x := by
  rw [brauerLocal_apply_inr, ← ConcreteCategory.comp_apply, gsBrauerInfl_comp_unitsLocalRes]

section Descent

def gsLift (τ : galUnramifiedOutside K.1 ℚ̄ S) : K.1.fixingSubgroup :=
  galToFixing K (τ.liftNormal ℚ̄)

theorem gsRestrict_gsLift : Function.RightInverse (gsLift K S) (gsRestrict K S) := by
  intro τ
  refine AlgEquiv.ext fun y => Subtype.ext ?_
  rw [gsRestrict_apply]
  exact AlgEquiv.liftNormal_commutes τ ℚ̄ y

variable (E : FiniteSubfield) [Fact (K ≤ E)] [IsGalois K.1 E.1]

abbrev fixingSubgroupOf : Subgroup K.1.fixingSubgroup :=
  E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup

instance normal_fixingSubgroupOf : (fixingSubgroupOf K E).Normal :=
  normal_subgroupOf_of_isGalois (K := K) (E := E)

variable {E}

theorem ker_gsRestrict_le (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    (gsRestrict K S).ker ≤ (QuotientGroup.mk' (fixingSubgroupOf K E)).ker := by
  intro σ hσ
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h := congrArg (fun τ : galUnramifiedOutside K.1 ℚ̄ S =>
    ((τ ⟨x, hE x hx⟩ : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) (MonoidHom.mem_ker.1 hσ)
  rw [gsRestrict_apply] at h
  exact h

def gsToQuotient (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    galUnramifiedOutside K.1 ℚ̄ S →* K.1.fixingSubgroup ⧸ fixingSubgroupOf K E :=
  (gsRestrict K S).liftOfRightInverse (gsLift K S) (gsRestrict_gsLift K S)
    ⟨QuotientGroup.mk' (fixingSubgroupOf K E), ker_gsRestrict_le K S hE⟩

theorem gsToQuotient_comp (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    (gsToQuotient K S hE).comp (gsRestrict K S) = QuotientGroup.mk' (fixingSubgroupOf K E) :=
  MonoidHom.liftOfRightInverse_comp _ _ _ _

theorem continuous_gsToQuotient (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    Continuous (gsToQuotient K S hE) := by
  have : T2Space (galUnramifiedOutside K.1 ℚ̄ S) := galois_t2Space K.1 (maxUnramifiedOutside K.1 ℚ̄ S)
  have hq : Topology.IsQuotientMap (gsRestrict K S) :=
    ((continuous_gsRestrict K S).isClosedMap).isQuotientMap (continuous_gsRestrict K S)
      (gsRestrict_gsLift K S).surjective
  rw [hq.continuous_iff]
  change Continuous ((gsToQuotient K S hE).comp (gsRestrict K S))
  rw [gsToQuotient_comp]
  exact continuous_quotientGroup_mk' _

instance isDiscreteRep_quotientToInvariants_fixingSubgroupOf :
    IsDiscreteRep ((unitsLimitRep K).quotientToInvariants (fixingSubgroupOf K E)) :=
  isDiscreteRep_quotientToInvariants_of_normal _ _

variable (E) in

abbrev unitsInvariantsOf :=
  Representation.invariants ((unitsLimitRep K).ρ.comp (fixingSubgroupOf K E).subtype)

omit [IsGalois K.1 E.1] in

theorem mem_of_mem_invariants (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (a : unitsInvariantsOf K E) :
    (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  refine hE _ ?_
  rw [← InfiniteGalois.fixedField_fixingSubgroup E.1, IntermediateField.mem_fixedField_iff]
  intro g hg
  have hK : g ∈ K.1.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (Fact.out : K ≤ E) hg
  have h := a.2 ⟨⟨g, hK⟩, Subgroup.mem_subgroupOf.2 hg⟩
  exact congrArg (fun z : Additive ℚ̄ˣ => ((Additive.toMul z : ℚ̄ˣ) : ℚ̄)) h

def invariantsToMaxUnitsFun (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    unitsInvariantsOf K E →+ Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ where
  toFun a := Additive.ofMul (Units.mk0
      (⟨(((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄), mem_of_mem_invariants K S hE a⟩ :
        maxUnramifiedOutside K.1 ℚ̄ S)
      (fun h => (Additive.toMul (a : Additive ℚ̄ˣ)).ne_zero (congrArg Subtype.val h)))
  map_zero' := Additive.toMul.injective (Units.ext (Subtype.ext rfl))
  map_add' _ _ := Additive.toMul.injective (Units.ext (Subtype.ext rfl))

omit [IsGalois K.1 E.1] in
theorem coe_invariantsToMaxUnitsFun (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (a : unitsInvariantsOf K E) :
    ((((Additive.toMul (invariantsToMaxUnitsFun K S hE a)) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
      maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) :=
  rfl

theorem coe_quotientToInvariants_mk (σ : K.1.fixingSubgroup) (a : unitsInvariantsOf K E) :
    (((Additive.toMul ((((unitsLimitRep K).ρ.quotientToInvariants (fixingSubgroupOf K E))
      (QuotientGroup.mk σ) a : unitsInvariantsOf K E) : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) =
      (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) :=
  rfl

theorem invariantsToMaxUnitsFun_smul (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (τ : galUnramifiedOutside K.1 ℚ̄ S) (a : unitsInvariantsOf K E) :
    invariantsToMaxUnitsFun K S hE
        ((((unitsLimitRep K).quotientToInvariants (fixingSubgroupOf K E)).ρ (gsToQuotient K S hE τ)) a) =
      (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))).ρ τ
        (invariantsToMaxUnitsFun K S hE a) := by
  have hτ := gsRestrict_gsLift K S τ
  have h1 : gsToQuotient K S hE τ = QuotientGroup.mk (gsLift K S τ) := by
    calc gsToQuotient K S hE τ = gsToQuotient K S hE (gsRestrict K S (gsLift K S τ)) := by rw [hτ]
      _ = QuotientGroup.mk (gsLift K S τ) := DFunLike.congr_fun (gsToQuotient_comp K S hE) _
  rw [h1]
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  have h2 := gsRestrict_apply K S (gsLift K S τ) ⟨_, mem_of_mem_invariants K S hE a⟩
  rw [hτ] at h2
  exact h2.symm

def invariantsToMaxUnits (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    Rep.res (gsToQuotient K S hE) ((unitsLimitRep K).quotientToInvariants (fixingSubgroupOf K E)) ⟶
      uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) :=
  Rep.ofHom ⟨(invariantsToMaxUnitsFun K S hE).toIntLinearMap, fun τ =>
    LinearMap.ext fun a => invariantsToMaxUnitsFun_smul K S hE τ a⟩

theorem invariantsToMaxUnits_comp_gsBrauerInfl (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    cohomologyMapAlong (gsToQuotient K S hE) (continuous_gsToQuotient K S hE)
      (invariantsToMaxUnits K S hE) 2 ≫ gsBrauerInfl K S 2 =
      cohomologyInfl (unitsLimitRep K) (fixingSubgroupOf K E) 2 := by
  rw [gsBrauerInfl, ← cohomologyMapAlong_comp, cohomologyInfl]
  refine cohomologyMapAlong_congr _ _ _ _ (gsToQuotient_comp K S hE) (fun a => ?_) 2
  apply Additive.toMul.injective
  apply Units.ext
  exact coe_invariantsToMaxUnitsFun K S hE a

theorem exists_gsBrauerInfl_eq_of_unitsResField_eq_zero
    (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (x : cohomology (unitsLimitRep K) 2)
    (hx : (unitsResField K E 2).hom x = 0) : ∃ y, (gsBrauerInfl K S 2).hom y = x := by
  have hN : IsClosed ((fixingSubgroupOf K E : Subgroup K.1.fixingSubgroup) : Set K.1.fixingSubgroup) :=
    Subgroup.isClosed_of_isOpen _ isOpen_subgroupOf_fixingSubgroup
  have hex := (infRes_exact (unitsLimitRep K) (fixingSubgroupOf K E) hN (q := 2) two_ne_zero
    fun i hi0 hi2 => by
      obtain rfl : i = 1 := by omega
      exact isZero_cohomology_one_res_subgroupOf).2
  have hmem : x ∈ LinearMap.range (cohomologyInfl (unitsLimitRep K) (fixingSubgroupOf K E) 2).hom := by
    rw [hex, LinearMap.mem_ker]
    exact (unitsResField_eq_zero_iff 2 x).1 hx
  obtain ⟨z, rfl⟩ := hmem
  refine ⟨(cohomologyMapAlong (gsToQuotient K S hE) (continuous_gsToQuotient K S hE)
    (invariantsToMaxUnits K S hE) 2).hom z, ?_⟩
  rw [← ConcreteCategory.comp_apply, invariantsToMaxUnits_comp_gsBrauerInfl]

end Descent

section Split

variable {K S}

theorem unitsResField_comp_unitsResField {E M : FiniteSubfield} [Fact (K ≤ E)] [Fact (E ≤ M)]
    [Fact (K ≤ M)] (n : ℕ) : unitsResField K E n ≫ unitsResField E M n = unitsResField K M n := by
  rw [unitsResField, unitsResField, ← cohomologyMapAlong_comp, unitsResField]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext; rfl) (fun _ => rfl) n

theorem natCast_pow_not_mem_of_forall {ℓ : ℕ}
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (b : ℕ) :
    ∀ v ∉ S, (((ℓ ^ b : ℕ) : ℕ) : 𝓞 K.1) ∉ v.asIdeal := by
  intro v hv h
  rw [Nat.cast_pow] at h
  exact hv (hS v (v.isPrime.mem_of_pow_mem _ h))

theorem mem_maxUnramifiedOutside_of_mem_rootsOfUnityField {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (b : ℕ) :
    ∀ x ∈ Cyclotomic.rootsOfUnityField (ℓ ^ b), x ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  have hle : Cyclotomic.rootsOfUnityField (ℓ ^ b) ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ :=
    IntermediateField.adjoin_le_iff.2 fun y hy =>
      mem_maxUnramifiedOutside_of_pow_eq_one S (pow_ne_zero _ hℓ.ne_zero)
        (natCast_pow_not_mem_of_forall hS b) hy
  exact fun x hx => hle hx

theorem mem_maxUnramifiedOutside_of_mem_compositum {F : FiniteSubfield}
    (hF : ∀ x ∈ F.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    ∀ x ∈ (CyclotomicSymbol.compositum K F).1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  have hle : (CyclotomicSymbol.compositum K F).1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ :=
    sup_le (fun x hx => (maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem (⟨x, hx⟩ : K.1)) fun x hx => hF x hx
  exact fun x hx => hle hx

theorem rootsOfUnityField_pow_le {ℓ : ℕ} {a b : ℕ} (hab : a ≤ b) :
    Cyclotomic.rootsOfUnityField (ℓ ^ a) ≤ Cyclotomic.rootsOfUnityField (ℓ ^ b) := by
  refine IntermediateField.adjoin_le_iff.2 fun y hy => IntermediateField.subset_adjoin ℚ _ ?_
  change y ^ ℓ ^ b = 1
  change y ^ ℓ ^ a = 1 at hy
  obtain ⟨c, hc⟩ := pow_dvd_pow ℓ hab
  rw [hc, pow_mul, hy, one_pow]

end Split

theorem exists_gsBrauerInfl_eq (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (x : cohomology (unitsLimitRep K) 2) (k : ℕ) (hx : ℓ ^ k • x = 0) :
    ∃ y, (gsBrauerInfl K S 2).hom y = x := by
  classical
  have hℓ2 : 2 < ℓ ^ 2 := by nlinarith [hℓ.two_le]
  have : NeZero (ℓ ^ 2) := ⟨pow_ne_zero _ hℓ.ne_zero⟩

  let F₂ : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField (ℓ ^ 2), inferInstance⟩
  let K' : FiniteSubfield := CyclotomicSymbol.compositum K F₂
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact (F₂ ≤ K') := CyclotomicSymbol.fact_le_compositum_right K F₂
  have : IsTotallyComplex F₂.1 := IsCyclotomicExtension.Rat.isTotallyComplex (n := ℓ ^ 2) F₂.1 hℓ2
  let _ : Algebra F₂.1 K'.1 := FiniteSubfield.algebraOfLE (Fact.out : F₂ ≤ K')
  have : IsTotallyComplex K'.1 := NumberField.isTotallyComplex_of_algebra (F := F₂.1) K'.1
  obtain ⟨ι'⟩ := nonempty_localEmbeddings K'
  set x' := (unitsResField K K' 2).hom x with hx'
  have hm : (ℓ ^ k) • x' = 0 := by rw [hx', ← map_nsmul, hx, map_zero]

  let T : Finset (HeightOneSpectrum (𝓞 K'.1)) :=
    (brauerLocal ι' x').support.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨r, ⟨N, hr⟩, hdeg⟩ :=
    CyclotomicLayer.exists_pow_dvd_finrank_cyclotomicLayer K' T (pow_ne_zero k hℓ.ne_zero)
  let E' : FiniteSubfield := CyclotomicLayer.cyclotomicLayer K' r
  have hsplit : (unitsResField K' E' 2).hom x' = 0 := by
    refine unitsResField_eq_zero_of_dvd_finrank ι' x' (ℓ ^ k) hm (fun v => ?_) fun v hv w => ?_
    · have := subsingleton_cohomology_two_of_isComplex v (IsTotallyComplex.isComplex v)
      exact Subsingleton.elim (α := cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) _ _
    · exact hdeg v (by rw [Finset.mem_preimage, DFinsupp.mem_support_iff]; exact hv) w

  let a := k * (N + 1)
  let b := a + Cyclotomic.unitsLevel ℓ + 2
  have : NeZero (ℓ ^ b) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  let F : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField (ℓ ^ b), inferInstance⟩
  let E : FiniteSubfield := CyclotomicSymbol.compositum K F
  have hrq : r = Cyclotomic.primePowPNat ℓ a := by
    apply PNat.eq
    rw [hr, Cyclotomic.coe_primePowPNat, ← pow_mul]
  have hF₂F : F₂.1 ≤ F.1 := rootsOfUnityField_pow_le (by omega)
  have hZF : (CyclotomicLayer.zhatLayer r).1 ≤ F.1 := by
    rw [hrq, CyclotomicLayer.zhatLayer_coe]
    exact (CyclotomicLayer.zhatLayerField_le_rootsOfUnityField ⟨ℓ, hℓ⟩ a).trans
      (rootsOfUnityField_pow_le (a := a + Cyclotomic.unitsLevel ℓ) (b := b) (by omega))
  have hE'E : E' ≤ E := by
    change (K.1 ⊔ F₂.1) ⊔ (CyclotomicLayer.zhatLayer r).1 ≤ K.1 ⊔ F.1
    exact sup_le (sup_le le_sup_left (hF₂F.trans le_sup_right)) (hZF.trans le_sup_right)
  have : Fact (E' ≤ E) := ⟨hE'E⟩
  have hKE : ∀ y ∈ E.1, y ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    mem_maxUnramifiedOutside_of_mem_compositum
      (mem_maxUnramifiedOutside_of_mem_rootsOfUnityField hℓ hS b)
  have hres : (unitsResField K E 2).hom x = 0 := by
    have hKE' : Fact (K ≤ E') := ⟨(Fact.out : K ≤ K').trans (Fact.out : K' ≤ E')⟩
    have h1 := unitsResField_comp_unitsResField (K := K) (E := E') (M := E) 2
    have h2 := unitsResField_comp_unitsResField (K := K) (E := K') (M := E') 2
    rw [← h1, ConcreteCategory.comp_apply, ← h2, ConcreteCategory.comp_apply]
    change (unitsResField E' E 2).hom ((unitsResField K' E' 2).hom x') = 0
    rw [hsplit, map_zero]
  exact exists_gsBrauerInfl_eq_of_unitsResField_eq_zero K S hKE x hres

end

end GroundTheory.ProfCoh
