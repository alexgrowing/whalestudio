import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LevelCyclic
import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderInfRes
import GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassEquivIdeleClassMapOfComm
import GroundTheory.TateCohomology.InfRes
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits GroundTheory.Global NumberField Module IntermediateField

section Tower

variable (K F M : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Field M]
  [NumberField M] [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]

omit [NumberField K] in

theorem smul_ideleClassMap_restrictNormal [Normal K F] (σ : Gal(M/K)) (c : IdeleClassGroup F) :
    σ • ideleClassMap F M c = ideleClassMap F M (AlgEquiv.restrictNormalHom F σ • c) :=
  ideleClassEquiv_ideleClassMap_of_comm (AlgEquiv.restrictNormalHom F σ : F ≃+* F) (σ : M ≃+* M)
    (fun l => (AlgEquiv.restrictNormal_commutes σ F l).symm) c

variable [Normal K F] [IsGalois K M]

noncomputable def classFixingCohomologyIso (n : ℕ) :
    groupCohomology (ideleClassRep F M) n ≅
      groupCohomology (Rep.res (galFixing K F M).subtype (ideleClassRep K M)) n :=
  groupCohomology.mapIso (galFixingEquiv K F M) (LinearEquiv.refl _ _)
    (fun _ => LinearMap.ext fun _ => rfl) n

omit [NumberField K] [NumberField F] [IsGalois K M] in

theorem isZero_groupCohomology_one_classFixing
    (h : IsZero (groupCohomology (ideleClassRep F M) 1)) :
    IsZero (groupCohomology (Rep.res (galFixing K F M).subtype (ideleClassRep K M)) 1) :=
  h.of_iso (classFixingCohomologyIso K F M 1).symm

omit [NumberField K] [IsGalois K M] in

theorem smul_ideleClassMap_of_mem_galFixing (g : galFixing K F M) (c : IdeleClassGroup F) :
    (g : Gal(M/K)) • ideleClassMap F M c = ideleClassMap F M c := by
  rw [smul_ideleClassMap_restrictNormal, MonoidHom.mem_ker.1 g.2, one_smul]

noncomputable def classToInvariants :
    (ideleClassRep K F) →ₗ[ℤ]
      Representation.invariants ((ideleClassRep K M).ρ.comp (galFixing K F M).subtype) :=
  LinearMap.codRestrict _
    ((MonoidHom.toAdditive (ideleClassMap F M)).toIntLinearMap :
      (ideleClassRep K F) →ₗ[ℤ] (ideleClassRep K M)) fun x g =>
    congrArg Additive.ofMul
      (smul_ideleClassMap_of_mem_galFixing K F M g (Additive.toMul (α := IdeleClassGroup F) x))

omit [NumberField K] in

theorem classToInvariants_bijective : Function.Bijective (classToInvariants K F M) := by
  have : IsGalois F M := IsGalois.tower_top_of_isGalois K F M
  constructor
  · intro x y h
    have h' : ideleClassMap F M (Additive.toMul (α := IdeleClassGroup F) x) =
        ideleClassMap F M (Additive.toMul (α := IdeleClassGroup F) y) :=
      congrArg (fun v => Additive.toMul (α := IdeleClassGroup M) v.1) h
    exact Additive.toMul.injective (ideleClassMap_injective h')
  · intro v
    have hfix : ∀ τ : Gal(M/F), τ • Additive.toMul (α := IdeleClassGroup M) v.1 =
        Additive.toMul (α := IdeleClassGroup M) v.1 := by
      intro τ
      have := v.2 ⟨galRestrictScalars K F M τ, (range_galRestrictScalars K F M) ▸ ⟨τ, rfl⟩⟩
      exact congrArg (Additive.toMul (α := IdeleClassGroup M)) this
    obtain ⟨c, hc⟩ := (forall_smul_eq_iff_mem_range_ideleClassMap
      (Additive.toMul (α := IdeleClassGroup M) v.1)).1 hfix
    exact ⟨Additive.ofMul c, Subtype.ext (congrArg Additive.ofMul hc)⟩

noncomputable def classInvariantsEquiv :
    (ideleClassRep K F) ≃ₗ[ℤ]
      Representation.invariants ((ideleClassRep K M).ρ.comp (galFixing K F M).subtype) :=
  LinearEquiv.ofBijective _ (classToInvariants_bijective K F M)

noncomputable def classQuotientCohomologyIso (n : ℕ) :
    groupCohomology (ideleClassRep K F) n ≅
      groupCohomology ((ideleClassRep K M).quotientToInvariants (galFixing K F M)) n :=
  groupCohomology.mapIso (galQuotientEquiv K F M).symm (classInvariantsEquiv K F M) (fun g => by
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) M g
    have hq : (galQuotientEquiv K F M).symm (AlgEquiv.restrictNormalHom F σ) =
        (σ : Gal(M/K) ⧸ galFixing K F M) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hq]
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact congrArg Additive.ofMul
      (smul_ideleClassMap_restrictNormal K F M σ
        (Additive.toMul (α := IdeleClassGroup F) x)).symm) n

variable {K F M}

omit [NumberField K] in

theorem isZero_groupCohomology_one_ideleClassRep_of_tower
    (hF : IsZero (groupCohomology (ideleClassRep K F) 1))
    (hM : IsZero (groupCohomology (ideleClassRep F M) 1)) :
    IsZero (groupCohomology (ideleClassRep K M) 1) := by
  have hS := isZero_groupCohomology_one_classFixing K F M hM
  have hQ : IsZero (groupCohomology ((ideleClassRep K M).quotientToInvariants
      (galFixing K F M)) 1) := hF.of_iso (classQuotientCohomologyIso K F M 1).symm
  have hex := GroundTheory.GroupCoh.range_inflation_eq_ker_restriction (A := ideleClassRep K M)
    (S := galFixing K F M) one_ne_zero fun i hi hi1 => absurd hi1 (by omega)
  rw [ModuleCat.isZero_iff_subsingleton] at hS hQ ⊢
  have hzero : ∀ x : groupCohomology (ideleClassRep K M) 1, x = 0 := by
    intro x
    have hx : x ∈ LinearMap.ker
        (GroundTheory.GroupCoh.restriction (ideleClassRep K M) (galFixing K F M) 1).hom := by
      rw [LinearMap.mem_ker]
      exact Subsingleton.elim _ _
    rw [← hex] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y => by rw [hzero x, hzero y]⟩

theorem natCard_groupCohomology_two_ideleClassRep_dvd_of_tower
    (hM1 : IsZero (groupCohomology (ideleClassRep F M) 1))
    (hM2 : Nat.card (groupCohomology (ideleClassRep F M) 2) ∣ finrank F M)
    (hF2 : Nat.card (groupCohomology (ideleClassRep K F) 2) ∣ finrank K F) :
    Nat.card (groupCohomology (ideleClassRep K M) 2) ∣ finrank K M := by
  have h1 := isZero_groupCohomology_one_classFixing K F M hM1
  have hinj := GroundTheory.GroupCoh.inflation_two_injective (A := ideleClassRep K M)
    (S := galFixing K F M) h1
  have hex := GroundTheory.GroupCoh.range_inflation_two_eq_ker_restriction (A := ideleClassRep K M)
    (S := galFixing K F M) h1
  set res := (GroundTheory.GroupCoh.restriction (ideleClassRep K M) (galFixing K F M) 2).hom
  set infl := (GroundTheory.GroupCoh.inflation (ideleClassRep K M) (galFixing K F M) 2).hom

  have hcard : Nat.card (groupCohomology (ideleClassRep K M) 2) =
      Nat.card (LinearMap.range res) * Nat.card (LinearMap.ker res) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker res),
      Nat.card_congr (LinearMap.quotKerEquivRange res).toEquiv, mul_comm]

  have hker : Nat.card (LinearMap.ker res) =
      Nat.card (groupCohomology (ideleClassRep K F) 2) := by
    rw [← hex, ← Nat.card_congr (LinearEquiv.ofInjective infl hinj).toEquiv]
    exact (Nat.card_congr (classQuotientCohomologyIso K F M 2).toLinearEquiv.toEquiv).symm

  have hrange : Nat.card (LinearMap.range res) ∣
      Nat.card (groupCohomology (ideleClassRep F M) 2) := by
    rw [Nat.card_congr (classFixingCohomologyIso K F M 2).toLinearEquiv.toEquiv]
    exact AddSubgroup.card_addSubgroup_dvd_card (LinearMap.range res).toAddSubgroup
  rw [hcard, hker, ← Module.finrank_mul_finrank K F M, mul_comm (finrank K F)]
  exact Nat.mul_dvd_mul (hrange.trans hM2) hF2

end Tower

section PGroup

theorem ideleClassRep_of_isPGroup_of_finrank (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [IsGalois K L], IsPGroup p Gal(L/K) → finrank K L = n →
      IsZero (groupCohomology (ideleClassRep K L) 1) ∧
        Nat.card (groupCohomology (ideleClassRep K L) 2) ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L _ _ _ _ _ _ hp hn
  subst hn
  by_cases hcyc : IsCyclic Gal(L/K)
  · exact ⟨isZero_groupCohomology_one_ideleClassRep_of_isCyclic,
      natCard_groupCohomology_two_ideleClassRep_of_isCyclic.dvd⟩
  have : Group.IsNilpotent Gal(L/K) := hp.isNilpotent
  obtain ⟨N, hN, hbot, htop⟩ := exists_normal_ne_bot_ne_top_of_not_isCyclic hcyc
  have hpos : 0 < finrank K (fixedField N) := Module.finrank_pos
  have hLE : finrank (fixedField N) L = Nat.card N := finrank_fixedField_eq_card N
  have hmul := Module.finrank_mul_finrank K (fixedField N) L
  have hcardG : Nat.card Gal(L/K) = finrank K L := IsGalois.card_aut_eq_finrank K L
  have hNlt : Nat.card N < finrank K L := by
    rw [← hcardG]
    exact lt_of_le_of_ne (Subgroup.card_le_card_group N)
      fun h => htop ((Subgroup.card_eq_iff_eq_top N).1 h)
  have hN1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hbot
  have hpL : IsPGroup p Gal(L/fixedField N) :=
    (hp.to_subgroup N).of_equiv (subgroupEquivGalFixedField N)
  have hpE : IsPGroup p Gal(fixedField N/K) :=
    hp.of_surjective (AlgEquiv.restrictNormalHom (fixedField N))
      (AlgEquiv.restrictNormalHom_surjective L)
  obtain ⟨hL1, hL2⟩ := ih _ (by rw [hLE]; exact hNlt) (fixedField N) L hpL rfl
  obtain ⟨hE1, hE2⟩ := ih _ (by rw [← hmul, hLE]; exact lt_mul_right hpos hN1) K (fixedField N)
    hpE rfl
  exact ⟨isZero_groupCohomology_one_ideleClassRep_of_tower hE1 hL1,
    natCard_groupCohomology_two_ideleClassRep_dvd_of_tower hL1 hL2 hE2⟩

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem isZero_groupCohomology_one_ideleClassRep_of_isPGroup {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p Gal(L/K)) : IsZero (groupCohomology (ideleClassRep K L) 1) :=
  (ideleClassRep_of_isPGroup_of_finrank p _ K L hp rfl).1

theorem natCard_groupCohomology_two_ideleClassRep_dvd_of_isPGroup {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p Gal(L/K)) :
    Nat.card (groupCohomology (ideleClassRep K L) 2) ∣ finrank K L :=
  (ideleClassRep_of_isPGroup_of_finrank p _ K L hp rfl).2

end PGroup

end GroundTheory.ProfCoh
