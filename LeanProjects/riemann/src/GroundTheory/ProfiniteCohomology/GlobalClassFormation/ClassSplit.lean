import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.CupDecompositionGlobal
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassLevels
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ResLocal
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.NatCardGroupCohomologyTwoIdeleClassRepDvd
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LevelCyclic
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Res

variable (K E : FiniteSubfield) [Fact (K ≤ E)]

def classResMor : Rep.res (fixingIncl K E) (classLimitRep K) ⟶ classLimitRep E :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def classResField (n : ℕ) : cohomology (classLimitRep K) n ⟶ cohomology (classLimitRep E) n :=
  cohomologyMapAlong (fixingIncl K E) (continuous_fixingIncl K E) (classResMor K E) n

end Res

variable {K E : FiniteSubfield} [Fact (K ≤ E)] [IsGalois K.1 E.1]

attribute [local instance] normal_subgroupOf_of_isGalois

variable (K E) in

def quotGalEquiv :
    (K.1.fixingSubgroup ⧸ E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) ≃* Gal(E.1/K.1) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_restrictHom (F := K) (E := E)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (restrictHom_surjective (F := K) (E := E)))

theorem quotGalEquiv_mk (g : K.1.fixingSubgroup) :
    quotGalEquiv K E (QuotientGroup.mk g) = restrictHom (E := E) g :=
  rfl

instance isDiscreteRep_res_classLimitRep (S : Subgroup K.1.fixingSubgroup) :
    IsDiscreteRep (Rep.res S.subtype (classLimitRep K)) :=
  isDiscreteRep_res_res classRep K.1.fixingSubgroup S

omit [Fact (K ≤ E)] [IsGalois K.1 E.1] in

theorem mem_invariants_of (c : IdeleClassGroup E.1) :
    Additive.ofMul (IdeleClassLimit.of E c) ∈
      ((Rep.res (E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).subtype (classLimitRep K)).ρ).invariants :=
  fun h => congrArg Additive.ofMul (IdeleClassLimit.smul_of_eq_of_mem_fixingSubgroup
    (Subgroup.mem_subgroupOf.1 h.2) c)

variable (K E) in

def classInvMor : Rep.res (quotGalEquiv K E).toMonoidHom (ideleClassRep K.1 E.1) ⟶
    (classLimitRep K).quotientToInvariants (E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) :=
  Rep.ofHom ⟨LinearMap.codRestrict _ (MonoidHom.toAdditive (IdeleClassLimit.of E)).toIntLinearMap
    fun c => mem_invariants_of (Additive.toMul c), fun q => by
    induction q using QuotientGroup.induction_on with
    | H g =>
      ext c
      change Additive.ofMul (IdeleClassLimit.of E
          (restrictHom (E := E) g • Additive.toMul (α := IdeleClassGroup E.1) c)) =
        Additive.ofMul ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • IdeleClassLimit.of E (Additive.toMul (α := IdeleClassGroup E.1) c))
      rw [IdeleClassLimit.smul_of_of_normal]⟩

theorem classInvMor_hom_apply (c : Additive (IdeleClassGroup E.1)) :
    (classInvMor K E).hom c = ⟨Additive.ofMul (IdeleClassLimit.of E (Additive.toMul c)),
      mem_invariants_of (Additive.toMul c)⟩ :=
  rfl

theorem classInvMor_bijective : Function.Bijective (classInvMor K E).hom := by
  constructor
  · intro c d h
    have h' : IdeleClassLimit.of E (Additive.toMul c) = IdeleClassLimit.of E (Additive.toMul d) := by
      have h2 : Additive.ofMul (IdeleClassLimit.of E (Additive.toMul (α := IdeleClassGroup E.1) c)) =
          Additive.ofMul (IdeleClassLimit.of E (Additive.toMul (α := IdeleClassGroup E.1) d)) :=
        congrArg Subtype.val h
      exact congrArg Additive.toMul h2
    exact congrArg Additive.ofMul (IdeleClassLimit.of_injective E h')
  · rintro ⟨z, hz⟩
    change Additive IdeleClassLimit at z
    have hz' : Additive.toMul z ∈ GroundTheory.LocalField.Abstract.fixedModule IdeleClassLimit E.1.fixingSubgroup := by
      intro g hg
      exact congrArg Additive.toMul (hz ⟨⟨g, IntermediateField.fixingSubgroup_le (Fact.out : K ≤ E) hg⟩,
        Subgroup.mem_subgroupOf.2 hg⟩)
    rw [IdeleClassLimit.fixedModule_fixingSubgroup] at hz'
    obtain ⟨c, hc⟩ := hz'
    exact ⟨Additive.ofMul c, Subtype.ext (congrArg Additive.ofMul hc)⟩

section Count

variable (K E)

theorem natCard_cohomology_quotientToInvariants :
    Nat.card (cohomology ((classLimitRep K).quotientToInvariants
      (E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup)) 2) =
      Nat.card (groupCohomology (ideleClassRep K.1 E.1) 2) := by
  have hopen : IsOpen ((E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup : Subgroup K.1.fixingSubgroup) :
      Set K.1.fixingSubgroup) := E.1.fixingSubgroup_isOpen.preimage continuous_subtype_val
  have : DiscreteTopology (K.1.fixingSubgroup ⧸ E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) :=
    QuotientGroup.discreteTopology hopen
  have hiso := isIso_cohomologyMapAlong_of_mulEquiv (quotGalEquiv K E) continuous_of_discreteTopology
    continuous_of_discreteTopology (classInvMor K E) (classInvMor_bijective) 2
  rw [← Nat.card_congr (cohomologyIsoGroupCohomology (ideleClassRep K.1 E.1) 2).toLinearEquiv.toEquiv]
  exact (Nat.card_congr (asIso (cohomologyMapAlong (quotGalEquiv K E).toMonoidHom
    continuous_of_discreteTopology (classInvMor K E) 2)).toLinearEquiv.toEquiv).symm

theorem natCard_ker_classResField :
    Nat.card (LinearMap.ker (classResField K E 2).hom) =
      Nat.card (groupCohomology (ideleClassRep K.1 E.1) 2) := by
  set N := E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup with hN
  have hle : E.1.fixingSubgroup ≤ K.1.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (Fact.out : K ≤ E)
  have hopen : IsOpen (N : Set K.1.fixingSubgroup) :=
    E.1.fixingSubgroup_isOpen.preimage continuous_subtype_val
  have hNc : IsClosed (N : Set K.1.fixingSubgroup) := Subgroup.isClosed_of_isOpen N hopen
  have h1 : Limits.IsZero (cohomology (Rep.res N.subtype (classLimitRep K)) 1) :=
    (isZero_cohomology_one_classLimitRep E).of_iso (asIso (cohomologyMapAlong
      (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom (continuous_subgroupOfEquivOfLe_symm hle)
      (resSubgroupOfHom hle classRep) 1))
  have hA : ∀ i, 0 < i → i < 2 → Limits.IsZero (cohomology (Rep.res N.subtype (classLimitRep K)) i) :=
    fun i hi hi2 => by
      obtain rfl : i = 1 := by omega
      exact h1
  have hr := range_cohomologyInfl_eq_ker_cohomologyRes (A := classLimitRep K) hNc two_ne_zero hA
  have hinj := cohomologyInfl_injective (A := classLimitRep K) hNc two_ne_zero hA
  have hker : ∀ x : cohomology (classLimitRep K) 2, x ∈ LinearMap.ker (classResField K E 2).hom ↔
      x ∈ LinearMap.range (cohomologyInfl (classLimitRep K) N 2).hom := by
    intro x
    rw [hr, LinearMap.mem_ker, LinearMap.mem_ker]
    exact cohomologyResLE_apply_eq_zero_iff hle classRep 2 x
  rw [← natCard_cohomology_quotientToInvariants K E]
  calc Nat.card (LinearMap.ker (classResField K E 2).hom)
      = Nat.card (LinearMap.range (cohomologyInfl (classLimitRep K) N 2).hom) :=
        Nat.card_congr (Equiv.subtypeEquivRight hker)
    _ = Nat.card (Set.range (cohomologyInfl (classLimitRep K) N 2).hom) := rfl
    _ = _ := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm

theorem natCard_ker_classResField_dvd :
    Nat.card (LinearMap.ker (classResField K E 2).hom) ∣ Module.finrank K.1 E.1 := by
  rw [natCard_ker_classResField]
  exact natCard_groupCohomology_two_ideleClassRep_dvd

theorem natCard_ker_classResField_of_isCyclic [IsCyclic Gal(E.1/K.1)] :
    Nat.card (LinearMap.ker (classResField K E 2).hom) = Module.finrank K.1 E.1 := by
  rw [natCard_ker_classResField]
  exact natCard_groupCohomology_two_ideleClassRep_of_isCyclic

end Count

end

end GroundTheory.ProfCoh
