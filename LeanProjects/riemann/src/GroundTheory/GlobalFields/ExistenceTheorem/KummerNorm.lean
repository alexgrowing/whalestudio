import Mathlib
import GroundTheory.GlobalFields.KummerTheory.Degree
import GroundTheory.GlobalFields.KummerTheory.Unramified
import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
import GroundTheory.GlobalFields.GlobalReciprocity.General
import GroundTheory.GlobalFields.PowerSubgroupIndex.Existence

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IdeleGroup IntermediateField
  GroundTheory.ProfCoh SemiLocal

noncomputable section

universe u

theorem IdeleGroup.finiteProj_mem_units_of_ord_eq_zero {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} {x : IdeleGroup K} (h : ord v x = 0) :
    finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  rw [ord_eq_zero_iff] at h
  refine (Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩
  · rw [coe_finiteProj]
    exact h.1
  · rw [← map_inv, coe_finiteProj]
    exact h.2

section SUnits

variable {K : Type u} [Field K] [NumberField K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]

omit [HasEnoughRootsOfUnity K n] in

theorem unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) :
    (unitsPow K n).subgroupOf (S.unit K) = (powMonoidHom n : S.unit K →* S.unit K).range := by
  ext e
  rw [Subgroup.mem_subgroupOf, mem_unitsPow, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    have hzu : z ∈ S.unit K := by
      intro v hv
      have he : v.valuationOfNeZero (e : Kˣ) = 1 := by
        have h := e.2 v hv
        rw [← valuationOfNeZero_eq] at h
        exact_mod_cast h
      have h1 : v.valuationOfNeZero z ^ n = 1 := by rw [← map_pow, hz, he]
      rw [← valuationOfNeZero_eq, (pow_eq_one_iff.1 h1).resolve_right (NeZero.ne n),
        WithZero.coe_one]
    exact ⟨⟨z, hzu⟩, Subtype.ext hz⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

theorem index_unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    ((unitsPow K n).subgroupOf (S.unit K)).index =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  rw [unitsPow_subgroupOf_sUnit, SUnit.index_range_powMonoidHom]

instance finiteIndex_unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    ((unitsPow K n).subgroupOf (S.unit K)).FiniteIndex :=
  ⟨by rw [index_unitsPow_subgroupOf_sUnit]; exact pow_ne_zero _ (NeZero.ne n)⟩

variable (K) in

abbrev sUnitKummerField (S : Set (HeightOneSpectrum (𝓞 K))) :
    IntermediateField K (AlgebraicClosure K) :=
  kummerExtension K n (AlgebraicClosure K) (S.unit K)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

instance sUnitKummerField.numberField : NumberField (sUnitKummerField K n S) :=
  NumberField.of_module_finite K _

instance sUnitKummerField.isAbelianGalois : IsAbelianGalois K (sUnitKummerField K n S) :=
  { toIsGalois := inferInstance, toIsMulCommutative := inferInstance }

theorem finrank_sUnitKummerField :
    Module.finrank K (sUnitKummerField K n S) =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  rw [finrank_kummerExtension, ← Subgroup.index, index_unitsPow_subgroupOf_sUnit]

end SUnits

section Symbol

attribute [local instance] galCommGroup

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S]

theorem ideleSymbol_adjoin_eq_one
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {a : Kˣ} (ha : a ∈ S.unit K) (β : sUnitKummerField K n S)
    (hβ : β ^ n = algebraMap K _ (a : K)) {x : IdeleGroup K} (hx : x ∈ powerSubgroup n S ∅) :
    ideleSymbol K (K⟮β⟯ : IntermediateField K (sUnitKummerField K n S)) x = 1 := by
  have hexpM : ∀ τ : Gal(sUnitKummerField K n S/K), τ ^ n = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (kummerExtension_exponent_dvd K n _ _)
  have hexp : ∀ τ : Gal(K⟮β⟯/K), τ ^ n = 1 := by
    intro τ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := K⟮β⟯)
      (E := sUnitKummerField K n S) τ
    rw [← map_pow, hexpM, map_one]
  have hβ' : (⟨β, mem_adjoin_simple_self K β⟩ : K⟮β⟯) ^ n = algebraMap K K⟮β⟯ (a : K) :=
    Subtype.ext (by exact hβ)
  have hgen : adjoin K {(⟨β, mem_adjoin_simple_self K β⟩ : K⟮β⟯)} = ⊤ :=
    lift_injective _ (by rw [lift_adjoin_simple, lift_top])
  have hinf : ∀ w, infiniteLocalSymbol K⟮β⟯ w (infiniteProj w x) = 1 := by
    intro w
    obtain ⟨t, ht⟩ := hx.2.1 w
    rw [← ht, powMonoidHom_apply, map_pow, hexp]
  have hfin : ∀ v, localSymbol K⟮β⟯ v (finiteProj v x) = 1 := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨t, ht⟩ := hx.1 v hv
      rw [← ht, powMonoidHom_apply, map_pow, hexp]
    · have hord : ord v x = 0 := hx.2.2 v (by simpa using hv)
      obtain ⟨w⟩ := nonempty_placesOver K⟮β⟯ v
      have hnv : (n : 𝓞 K) ∉ v.asIdeal := fun h ↦ hv (hS v h)
      have hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)) := by
        have h := ha v hv
        rw [← valuationOfNeZero_eq] at h
        rw [← valuationOfNeZero_eq, show v.valuationOfNeZero a = 1 by exact_mod_cast h]
        simp
      have he := Kummer.ramificationIdx_eq_one_of_pow_eq (M := K⟮β⟯) a hβ' hgen v hnv hav
        w.1.asIdeal
      exact units_le_ker_localSymbol K⟮β⟯ v w he (finiteProj_mem_units_of_ord_eq_zero hord)
  rw [ideleSymbol_apply, finprod_eq_one_of_forall_eq_one hfin,
    Finset.prod_eq_one fun w _ ↦ hinf w, mul_one]

theorem ideleSymbol_sUnitKummerField_eq_one
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {x : IdeleGroup K} (hx : x ∈ powerSubgroup n S ∅) :
    ideleSymbol K (sUnitKummerField K n S) x = 1 := by
  set M := sUnitKummerField K n S
  have hfix : ∀ (β : M) (a : Kˣ), a ∈ S.unit K →
      (β : AlgebraicClosure K) ^ n = algebraMap K _ (a : K) → ideleSymbol K M x β = β := by
    intro β a ha hβ
    have hβ' : β ^ n = algebraMap K M (a : K) := Subtype.ext hβ
    have h1 := restrictNormal_ideleSymbol (K⟮β⟯ : IntermediateField K M) M x
    rw [ideleSymbol_adjoin_eq_one hS ha β hβ' hx, AlgEquiv.restrictNormal_eq_one_iff] at h1
    exact h1 β (mem_adjoin_simple_self K β)
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin K (S := M)
    (s := {α : AlgebraicClosure K | ∃ a ∈ S.unit K, α ^ n = algebraMap K _ (a : K)}) rfl ?_
  rintro y ⟨a, ha, hy⟩
  exact hfix _ a ha hy

theorem map_powerSubgroup_le_range_ideleClassNorm
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerSubgroup n S ∅).map (IdeleClassGroup.mk K) ≤
      (ideleClassNorm K (sUnitKummerField K n S)).range := by
  rw [← ker_reciprocityMap, Subgroup.map_le_iff_le_comap]
  intro x hx
  rw [Subgroup.mem_comap, MonoidHom.mem_ker, reciprocityMap_mk]
  exact ideleSymbol_sUnitKummerField_eq_one hS hx

theorem range_ideleClassNorm_sUnitKummerField (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤) :
    (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range =
      (powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K) := by
  have hle := map_powerSubgroup_le_range_ideleClassNorm (n := n)
    (S := (S : Set (HeightOneSpectrum (𝓞 K)))) fun v hv ↦ Finset.mem_coe.2 (hS v hv)
  have h1 : (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range.index =
      n ^ (S.card + Fintype.card (InfinitePlace K)) := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative, finrank_sUnitKummerField,
      Nat.card_coe_set_eq, Set.ncard_coe_finset, add_comm]
  have h2 := index_map_powerSubgroup (n := n) S hS hJ
  have hrel := Subgroup.relIndex_mul_index hle
  rw [h1, h2] at hrel
  have hone : ((powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map
      (IdeleClassGroup.mk K)).relIndex
      (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range = 1 :=
    Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos n) _) (by rw [hrel, one_mul])
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hone) hle

end Symbol

end

end GroundTheory.Global
