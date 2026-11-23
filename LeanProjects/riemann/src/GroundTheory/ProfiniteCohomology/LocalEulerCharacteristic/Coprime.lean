import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Scalars
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CoprimeRegular
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CoprimeTwist
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.ModNEquivOfSurjectiveApplyModNRep
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveInvariants
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Cohomology
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.KummerOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField Representation ValuativeRel

section Card

variable (l : ℕ) [Fact l.Prime]

theorem natCard_eq_pow_finrank_zmod (V : Type*) [AddCommGroup V] [Module (ZMod l) V] [Finite V] :
    Nat.card V = l ^ Module.finrank (ZMod l) V := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod l) (V := V), ZMod.card]

theorem finrank_eq_of_natCard_zmod {V : Type*} [AddCommGroup V] [Module (ZMod l) V] [Finite V]
    {r : ℕ} (h : Nat.card V = l ^ r) : Module.finrank (ZMod l) V = r := by
  rw [natCard_eq_pow_finrank_zmod l V] at h
  exact Nat.pow_right_injective (Fact.out : l.Prime).two_le h

end Card

section Roots

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] (l : ℕ)

theorem nsmul_galRootsOfUnity_eq_zero (a : galRootsOfUnity.{0} K Ksep l) : l • a = 0 := by
  have key : ∀ b : Additive (rootsOfUnity l Ksep), l • b = 0 := fun b => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using (mem_rootsOfUnity l _).1 (Additive.toMul b).2)
  exact key a

noncomputable abbrev rootsRepZMod (U : Subgroup Gal(Ksep/K)) : Rep.{0} (ZMod l) U :=
  zmodRepOfTorsion l (Rep.res U.subtype (galRootsOfUnity.{0} K Ksep l))
    (nsmul_galRootsOfUnity_eq_zero (K := K) (Ksep := Ksep) l)

variable [IsSepClosure K Ksep]

theorem finrank_rootsRepZMod [Fact l.Prime] (hl : (l : K) ≠ 0) (U : Subgroup Gal(Ksep/K)) :
    Module.finrank (ZMod l) (rootsRepZMod (K := K) (Ksep := Ksep) l U) = 1 := by
  have hlp : l.Prime := Fact.out
  have : IsSepClosed Ksep := IsSepClosure.sep_closed K
  have : NeZero (l : Ksep) := ⟨by
    rw [← map_natCast (algebraMap K Ksep)]
    exact (map_ne_zero _).mpr hl⟩
  have : NeZero l := ⟨hlp.ne_zero⟩
  have hcard : Nat.card (rootsRepZMod (K := K) (Ksep := Ksep) l U) = l ^ 1 :=
    (Nat.card_congr (Additive.toMul (α := rootsOfUnity l Ksep))).trans
      ((HasEnoughRootsOfUnity.natCard_rootsOfUnity Ksep l).trans (pow_one l).symm)
  have : Finite (rootsRepZMod (K := K) (Ksep := Ksep) l U) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ hlp.ne_zero)
  exact finrank_eq_of_natCard_zmod l hcard

end Roots

section RootsSubgroupOf

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {l : ℕ}
  {U V : OpenSubgroup Gal(Ksep/K)}

omit [IsSepClosure K Ksep] in

theorem rootsRepZMod_ρ_of_mem
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (g : (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K))))
    (t : rootsRepZMod (K := K) (Ksep := Ksep) l U) :
    (rootsRepZMod (K := K) (Ksep := Ksep) l U).ρ g t = t := by
  have hg : (((g : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K))) ∈ (V : Subgroup Gal(Ksep/K)) :=
    Subgroup.mem_subgroupOf.1 g.2
  have key : ∀ s : Additive (rootsOfUnity l Ksep),
      (galRootsOfUnity.{0} K Ksep l).ρ ((g : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) s = s := by
    intro s
    rw [galRootsOfUnity_ρ_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rw [toMul_ofMul, coe_galRootsOfUnityHom_apply]
    have hs : (((Additive.toMul s : rootsOfUnity l Ksep) : Ksepˣ) : Ksep) ^ l = 1 := by
      have := (mem_rootsOfUnity l _).1 (Additive.toMul s).2
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    exact (mem_fixedField_iff _ _).1 (hμ _ hs) _ hg
  exact key t

variable (l) in

noncomputable def rootsCohomologyZModEquiv (n : ℕ) :
    cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) n ≃+
      cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (rootsRepZMod (K := K) (Ksep := Ksep) l U)) n :=
  cohomologyAddEquivOfEquiv
    (A := Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
      (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l)))
    (A' := Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
      (rootsRepZMod (K := K) (Ksep := Ksep) l U))
    (zmodRepOfTorsionEquiv l _ (nsmul_galRootsOfUnity_eq_zero (K := K) (Ksep := Ksep) l))
    (fun _ _ => rfl) n

theorem rootsCohomologyZModEquiv_cohomologyConj
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal] (n : ℕ)
    (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) n) :
    rootsCohomologyZModEquiv l n ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf
          (U : Subgroup Gal(Ksep/K))) n g).hom x) =
      (cohomologyConj (rootsRepZMod (K := K) (Ksep := Ksep) l U) ((V : Subgroup Gal(Ksep/K)).subgroupOf
          (U : Subgroup Gal(Ksep/K))) n g).hom (rootsCohomologyZModEquiv l n x) :=
  cohomologyAddEquivOfEquiv_cohomologyConj (A := Rep.res (U : Subgroup Gal(Ksep/K)).subtype
    (galRootsOfUnity.{0} K Ksep l)) (A' := rootsRepZMod (K := K) (Ksep := Ksep) l U)
    (zmodRepOfTorsionEquiv l _ (nsmul_galRootsOfUnity_eq_zero (K := K) (Ksep := Ksep) l))
    (fun _ _ => rfl) _ n g x

end RootsSubgroupOf

section Local

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {l : ℕ} {U V : OpenSubgroup Gal(Ksep/K)}

theorem finite_cohomology_roots_subgroupOf (hl : (l : K) ≠ 0) (h : V ≤ U)
    (n : ℕ) (hn : n ≤ 2) :
    Finite (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) n) := by
  have := finite_cohomology_rootsOfUnity_open K Ksep hl V n hn
  exact Finite.of_equiv _ (asIso (cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe
      (show (V : Subgroup Gal(Ksep/K)) ≤ U from h)).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm _) (resSubgroupOfHom _ (galRootsOfUnity.{0} K Ksep l))
      n)).toLinearEquiv.toEquiv.symm

end Local

section ZModLinear

variable {l : ℕ} {X Y : Type*} [AddCommGroup X] [Module (ZMod l) X] [AddCommGroup Y]
  [Module (ZMod l) Y]

noncomputable def addEquivZModLinear (φ : X ≃+ Y) : X ≃ₗ[ZMod l] Y :=
  { φ.toAddMonoidHom.toZModLinearMap l with
    invFun := φ.symm
    left_inv := φ.symm_apply_apply
    right_inv := φ.apply_symm_apply }

theorem addEquivZModLinear_apply (φ : X ≃+ Y) (x : X) : addEquivZModLinear (l := l) φ x = φ x :=
  rfl

end ZModLinear

section Assembly

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {l : ℕ} [Fact l.Prime] {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)
  [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

include h in

theorem toFun_cohomologyConjRep_eq
    (d : letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
      AdditiveFunction.{0} l (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
        (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K))))
    (i : ℕ)
    [Finite (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf
        (U : Subgroup Gal(Ksep/K))).subtype (rootsRepZMod (K := K) (Ksep := Ksep) l U)) i)]
    {Y : Type} [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y]
    (ρY : letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
      Representation (ZMod l) (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
        (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K))) Y)
    (φ : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf
        (U : Subgroup Gal(Ksep/K))).subtype (rootsRepZMod (K := K) (Ksep := Ksep) l U)) i ≃+ Y)
    (hφ : ∀ (g : (U : Subgroup Gal(Ksep/K))) x,
      φ ((cohomologyConj (rootsRepZMod (K := K) (Ksep := Ksep) l U) ((V : Subgroup Gal(Ksep/K)).subgroupOf
        (U : Subgroup Gal(Ksep/K))) i g).hom x) = ρY (fixedFieldGalHom h g) (φ x)) :
    haveI : CompactSpace ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) :=
      compactSpace_openSubgroup (openSubgroupOf U V)
    d.toFun _ ((cohomologyConjRep (rootsRepZMod (K := K) (Ksep := Ksep) l U)
        ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) i).comp
        (quotientFixedFieldGalEquiv h).symm.toMonoidHom) = d.toFun Y ρY := by
  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have : CompactSpace ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) :=
    compactSpace_openSubgroup (openSubgroupOf U V)
  refine d.toFun_congr _ _ (addEquivZModLinear φ) fun γ x => ?_
  obtain ⟨q, rfl⟩ := (quotientFixedFieldGalEquiv h).surjective γ
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [addEquivZModLinear_apply, addEquivZModLinear_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, cohomologyConjRep_mk, hφ,
      quotientFixedFieldGalEquiv_mk]

end Assembly

section Main

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  [ValuativeRel Ksep] [TopologicalSpace Ksep] [IsValuativeTopology Ksep] [ValuativeExtension K Ksep]
  {l : ℕ} [Fact l.Prime] {U V : OpenSubgroup Gal(Ksep/K)}

set_option maxHeartbeats 400000 in

theorem finrank_cohomology_alternating_sum_coprime (hl : (l : K) ≠ 0) (h : V ≤ U)
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]
    (hcop : Nat.Coprime ((V : Subgroup Gal(Ksep/K)).relIndex U) l)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (M : Rep.{0} (ZMod l) (U : Subgroup Gal(Ksep/K))) [IsDiscreteRep M] [Module.Finite (ZMod l) M]
    (hM : ∀ g : (U : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ V → ∀ m : M, M.ρ g m = m)
    {n : ℕ} (hn : Nat.card (𝒪[fixedField (U : Subgroup Gal(Ksep/K))] ⧸
      Ideal.span {(l : 𝒪[fixedField (U : Subgroup Gal(Ksep/K))])}) = l ^ n) :
    (Module.finrank (ZMod l) (cohomology M 0) : ℤ) - Module.finrank (ZMod l) (cohomology M 1) +
      Module.finrank (ZMod l) (cohomology M 2) = -(n * Module.finrank (ZMod l) M) := by
  classical
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩

  have : CompactSpace (U : Subgroup Gal(Ksep/K)) := compactSpace_openSubgroup U
  have : CompactSpace ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) :=
    compactSpace_openSubgroup (openSubgroupOf U V)
  have hT : ∀ (g : (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K))))
      (t : rootsRepZMod (K := K) (Ksep := Ksep) l U),
      (rootsRepZMod (K := K) (Ksep := Ksep) l U).ρ g t = t :=
    rootsRepZMod_ρ_of_mem hμ
  have hM' : ∀ (g : (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K)))) (m : M),
      M.ρ g m = m :=
    fun g m => hM g (Subgroup.mem_subgroupOf.1 g.2) m
  have hTr : Module.finrank (ZMod l) (rootsRepZMod (K := K) (Ksep := Ksep) l U) = 1 :=
    finrank_rootsRepZMod l hl _
  have hrel0 : (V : Subgroup Gal(Ksep/K)).relIndex U ≠ 0 := fun h0 => by
    rw [h0, Nat.coprime_zero_left] at hcop
    exact hlp.one_lt.ne' hcop
  have hP : (((openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K))).index : ZMod l)) ≠ 0 := by
    change (((V : Subgroup Gal(Ksep/K)).relIndex U : ℕ) : ZMod l) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hlp).1 hcop.symm
  have hkey := finrank_cohomology_eq_finrank_invariants (openSubgroupOf U V)
    (rootsRepZMod (K := K) (Ksep := Ksep) l U) M hT hM' hTr hP

  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have hcardΓ : Nat.card (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
      (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K))) =
      (V : Subgroup Gal(Ksep/K)).relIndex U :=
    (Nat.card_congr (quotientFixedFieldGalEquiv h).toEquiv).symm
  have : Finite (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
      fixedField (V : Subgroup Gal(Ksep/K))) :=
    Nat.finite_of_card_ne_zero (by rw [hcardΓ]; exact hrel0)
  have hΓ : Nat.Coprime (Nat.card (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
      (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K)))) l := by
    rw [hcardΓ]; exact hcop
  have : Module.Finite (ZMod l) (rootsRepZMod (K := K) (Ksep := Ksep) l U) :=
    Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite (ZMod l) (homRep (rootsRepZMod (K := K) (Ksep := Ksep) l U) M) :=
    inferInstanceAs (Module.Finite (ZMod l) (rootsRepZMod (K := K) (Ksep := Ksep) l U →ₗ[ZMod l] M))
  let σ := quotientRep (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K)))
    (homRep (rootsRepZMod (K := K) (Ksep := Ksep) l U) M) (homRep_ρ_of_mem _ _ _ hT hM')
  let d : AdditiveFunction.{0} l (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
      (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K))) :=
    AdditiveFunction.invariantsTensor.{0} l _ hΓ (σ.comp (quotientFixedFieldGalEquiv h).symm.toMonoidHom)

  have hstep : ∀ (i : ℕ) [Finite (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf
      (U : Subgroup Gal(Ksep/K))).subtype (rootsRepZMod (K := K) (Ksep := Ksep) l U)) i)],
      (Module.finrank (ZMod l) (cohomology M i) : ℤ) = d.toFun _
        ((cohomologyConjRep (rootsRepZMod (K := K) (Ksep := Ksep) l U)
          ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) i).comp
          (quotientFixedFieldGalEquiv h).symm.toMonoidHom) := by
    intro i _
    rw [hkey i, AdditiveFunction.invariantsTensor_apply]
    have hc : Representation.tprod ((cohomologyConjRep (rootsRepZMod (K := K) (Ksep := Ksep) l U)
        ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) i).comp
          (quotientFixedFieldGalEquiv h).symm.toMonoidHom)
        (σ.comp (quotientFixedFieldGalEquiv h).symm.toMonoidHom) =
        ((cohomologyConjRep (rootsRepZMod (K := K) (Ksep := Ksep) l U)
          ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) i).tprod σ).comp
          (quotientFixedFieldGalEquiv h).symm.toMonoidHom := rfl
    rw [hc, invariants_comp_of_surjective _ _ (quotientFixedFieldGalEquiv h).symm.surjective]

  have hX : ∀ i ≤ 2, Finite (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf
      (U : Subgroup Gal(Ksep/K))).subtype (rootsRepZMod (K := K) (Ksep := Ksep) l U)) i) :=
    fun i hi => by
      have := finite_cohomology_roots_subgroupOf (K := K) (Ksep := Ksep) hl h i hi
      exact Finite.of_equiv _ (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V)
        l i).toEquiv
  have hX0 := hX 0 (by norm_num)
  have hX1 := hX 1 (by norm_num)
  have hX2 := hX 2 (by norm_num)

  let φ0 := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V) l 0).symm.trans
    (cohomologyZeroRootsEquiv h l)
  have : Finite (TorsN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l) :=
    Finite.of_equiv _ φ0.toEquiv
  have e0 := toFun_cohomologyConjRep_eq h d 0 _ φ0 (fun g x => by
    obtain ⟨y, rfl⟩ := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V)
      l 0).surjective x
    simp only [φ0, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rw [← rootsCohomologyZModEquiv_cohomologyConj, AddEquiv.symm_apply_apply]
    exact cohomologyZeroRootsEquiv_cohomologyConj_gal h l g y)

  let φ1 := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V) l 1).symm.trans
    (cohomologyOneRootsEquiv h hl)
  have : Finite (ModN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l) :=
    Finite.of_equiv _ φ1.toEquiv
  have e1 := toFun_cohomologyConjRep_eq h d 1 _ φ1 (fun g x => by
    obtain ⟨y, rfl⟩ := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V)
      l 1).surjective x
    simp only [φ1, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rw [← rootsCohomologyZModEquiv_cohomologyConj, AddEquiv.symm_apply_apply]
    exact cohomologyOneRootsEquiv_cohomologyConj_gal h hl g y)

  let φ2 := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V) l 2).symm.trans
    ((cohomologyTwoRootsEquiv hl h).trans (AddEquiv.ulift.{0} (α := ZMod l)).symm)
  have e2 := toFun_cohomologyConjRep_eq h d 2
    (Representation.trivial (ZMod l) _ (ULift.{0} (ZMod l))) φ2 (fun g x => by
    obtain ⟨y, rfl⟩ := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V)
      l 2).surjective x
    simp only [φ2, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rw [← rootsCohomologyZModEquiv_cohomologyConj, AddEquiv.symm_apply_apply,
      cohomologyTwoRootsEquiv_cohomologyConj]
    rfl)

  have : IsScalarTower K (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) := Module.Finite.of_restrictScalars_finite K _ _
  have : ValuativeExtension (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) :=
    GroundTheory.LocalField.IntermediateField.valuativeExtension_inclusion (fixedField_le_fixedField h)
  have : IsGalois (fixedField (U : Subgroup Gal(Ksep/K))) (fixedField (V : Subgroup Gal(Ksep/K))) :=
    IsGalois.of_card_aut_eq_finrank (F := fixedField (U : Subgroup Gal(Ksep/K)))
      (E := fixedField (V : Subgroup Gal(Ksep/K))) (by rw [hcardΓ, relIndex_eq_finrank h])
  have hlE : (l : fixedField (U : Subgroup Gal(Ksep/K))) ≠ 0 := by
    rw [← map_natCast (algebraMap K (fixedField (U : Subgroup Gal(Ksep/K))))]
    exact (map_ne_zero _).mpr hl
  have hg := g_units_eq d hlE hn
  rw [d.g_eq] at hg
  have : Fintype (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
      fixedField (V : Subgroup Gal(Ksep/K))) := Fintype.ofFinite _
  have hreg : d.toFun (MonoidAlgebra (ZMod l) (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
      (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K))))
      (leftRegular (ZMod l) _) = Module.finrank (ZMod l) M := by
    rw [AdditiveFunction.invariantsTensor_apply, finrank_invariants_leftRegular_tprod]
    change ((Module.finrank (ZMod l) (rootsRepZMod (K := K) (Ksep := Ksep) l U →ₗ[ZMod l] M) : ℕ) : ℤ) = _
    rw [Module.finrank_linearMap, hTr, one_mul]
  rw [hstep 0, hstep 1, hstep 2, e0, e1, e2, ← hreg]
  change _ - _ + d.one = _
  linarith

set_option maxHeartbeats 400000 in
omit [ValuativeRel Ksep] [TopologicalSpace Ksep] [IsValuativeTopology Ksep]
  [ValuativeExtension K Ksep] in

theorem finite_cohomology_coprime (hl : (l : K) ≠ 0) (h : V ≤ U)
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]
    (hcop : Nat.Coprime ((V : Subgroup Gal(Ksep/K)).relIndex U) l)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (M : Rep.{0} (ZMod l) (U : Subgroup Gal(Ksep/K))) [IsDiscreteRep M] [Module.Finite (ZMod l) M]
    (hM : ∀ g : (U : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ V → ∀ m : M, M.ρ g m = m)
    (i : ℕ) (hi : i ≤ 2) : Finite (cohomology M i) := by
  have hlp : l.Prime := Fact.out
  have : CompactSpace (U : Subgroup Gal(Ksep/K)) := compactSpace_openSubgroup U
  have : CompactSpace ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) :=
    compactSpace_openSubgroup (openSubgroupOf U V)
  have hT : ∀ (g : (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K))))
      (t : rootsRepZMod (K := K) (Ksep := Ksep) l U),
      (rootsRepZMod (K := K) (Ksep := Ksep) l U).ρ g t = t :=
    rootsRepZMod_ρ_of_mem hμ
  have hM' : ∀ (g : (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K)))) (m : M),
      M.ρ g m = m :=
    fun g m => hM g (Subgroup.mem_subgroupOf.1 g.2) m
  have hTr : Module.finrank (ZMod l) (rootsRepZMod (K := K) (Ksep := Ksep) l U) = 1 :=
    finrank_rootsRepZMod l hl _
  have hP : (((openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K))).index : ZMod l)) ≠ 0 := by
    change (((V : Subgroup Gal(Ksep/K)).relIndex U : ℕ) : ZMod l) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hlp).1 hcop.symm
  have : Finite (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf
      (U : Subgroup Gal(Ksep/K))).subtype (rootsRepZMod (K := K) (Ksep := Ksep) l U)) i) := by
    have := finite_cohomology_roots_subgroupOf (K := K) (Ksep := Ksep) hl h i hi
    exact Finite.of_equiv _ (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V)
      l i).toEquiv
  have : Module.Finite (ZMod l) (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf
      (U : Subgroup Gal(Ksep/K))).subtype (rootsRepZMod (K := K) (Ksep := Ksep) l U)) i) :=
    Module.Finite.of_finite
  have : Module.Finite (ZMod l) (rootsRepZMod (K := K) (Ksep := Ksep) l U) :=
    Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite (ZMod l) (homRep (rootsRepZMod (K := K) (Ksep := Ksep) l U) M) :=
    inferInstanceAs (Module.Finite (ZMod l) (rootsRepZMod (K := K) (Ksep := Ksep) l U →ₗ[ZMod l] M))
  have : NeZero l := ⟨hlp.ne_zero⟩
  have := Module.finite_of_finite (ZMod l) (M := ((cohomologyConjRep
    (rootsRepZMod (K := K) (Ksep := Ksep) l U) (openSubgroupOf U V : Subgroup _) i).tprod
      (quotientRep (openSubgroupOf U V : Subgroup _) (homRep (rootsRepZMod (K := K) (Ksep := Ksep) l U) M)
        (homRep_ρ_of_mem _ _ _ hT hM'))).invariants)
  exact Finite.of_equiv _ (coprimeTwistEquiv (openSubgroupOf U V)
    (rootsRepZMod (K := K) (Ksep := Ksep) l U) M hT hM' hTr hP i).symm.toEquiv

theorem eulerChar_coprime (hl : (l : K) ≠ 0) (h : V ≤ U)
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]
    (hcop : Nat.Coprime ((V : Subgroup Gal(Ksep/K)).relIndex U) l)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (M : Rep.{0} (ULift.{0} ℤ) (U : Subgroup Gal(Ksep/K))) [IsDiscreteRep M] [Finite M]
    (hMl : ∀ m : M, l • m = 0)
    (hM : ∀ g : (U : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ V → ∀ m : M, M.ρ g m = m)
    {n : ℕ} (hn : Nat.card (𝒪[fixedField (U : Subgroup Gal(Ksep/K))] ⧸
      Ideal.span {(l : 𝒪[fixedField (U : Subgroup Gal(Ksep/K))])}) = l ^ n) :
    eulerChar M = ((Nat.card M : ℚ) ^ n)⁻¹ := by
  have hlp : l.Prime := Fact.out
  set MZ := zmodRepOfTorsion l M hMl
  have : Finite MZ := ‹Finite M›
  have : Module.Finite (ZMod l) MZ := Module.Finite.of_finite
  have hMZ : ∀ g : (U : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ V → ∀ m : MZ, MZ.ρ g m = m :=
    hM
  have hsum := finrank_cohomology_alternating_sum_coprime hl h hcop hμ MZ hMZ hn
  have hcard : ∀ i ≤ 2, Nat.card (cohomology M i) = l ^ Module.finrank (ZMod l) (cohomology MZ i) :=
    fun i hi => by
      have := finite_cohomology_coprime hl h hcop hμ MZ hMZ i hi
      rw [Nat.card_congr (cohomologyZModEquiv l M hMl i).toEquiv, natCard_eq_pow_finrank_zmod l]
  have hcardM : Nat.card M = l ^ Module.finrank (ZMod l) MZ := natCard_eq_pow_finrank_zmod l MZ
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast hlp.ne_zero
  rw [eulerChar_eq, hcard 0 (by norm_num), hcard 1 (by norm_num), hcard 2 (by norm_num), hcardM]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast (_ ^ _), ← zpow_natCast,
    ← zpow_mul, ← zpow_add₀ hl0, ← zpow_sub₀ hl0, ← zpow_neg]
  congr 1
  linarith

omit [ValuativeRel Ksep] [TopologicalSpace Ksep] [IsValuativeTopology Ksep]
  [ValuativeExtension K Ksep] in

theorem finite_cohomology_coprime_of_torsion (hl : (l : K) ≠ 0) (h : V ≤ U)
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]
    (hcop : Nat.Coprime ((V : Subgroup Gal(Ksep/K)).relIndex U) l)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (M : Rep.{0} (ULift.{0} ℤ) (U : Subgroup Gal(Ksep/K))) [IsDiscreteRep M] [Finite M]
    (hMl : ∀ m : M, l • m = 0)
    (hM : ∀ g : (U : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ V → ∀ m : M, M.ρ g m = m)
    (i : ℕ) (hi : i ≤ 2) : Finite (cohomology M i) := by
  have : Finite (zmodRepOfTorsion l M hMl) := ‹Finite M›
  have : Module.Finite (ZMod l) (zmodRepOfTorsion l M hMl) := Module.Finite.of_finite
  have := finite_cohomology_coprime hl h hcop hμ (zmodRepOfTorsion l M hMl) hM i hi
  exact Finite.of_equiv _ (cohomologyZModEquiv l M hMl i).symm.toEquiv

end Main

end GroundTheory.ProfCoh
