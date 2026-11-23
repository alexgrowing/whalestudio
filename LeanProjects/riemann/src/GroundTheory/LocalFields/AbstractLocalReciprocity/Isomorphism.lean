import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.IsoPGroup
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TransferOfCompSubtype

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger MulAction

section Transfer

theorem transfer_of_comp_subtype {Γ : Type*} [Group Γ] (H : Subgroup Γ) [H.FiniteIndex] (g : Γ) :
    ((Abelianization.of : Γ →* Abelianization Γ).comp H.subtype).transfer g =
      Abelianization.of g ^ H.index :=
  _root_.UpperTheory.Reformulated.B.Qe30.transfer_of_comp_subtype H g

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

theorem map_verlagerung {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L : Subgroup G).subgroupOf K').Normal] (hK'K : K' ≤ K)
    (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    Abelianization.map (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl)
        (verlagerung hK'K g) =
      Abelianization.of g ^ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range.index := by
  rw [verlagerung, map_transfer, ← transfer_of_comp_subtype]
  have e : (Abelianization.map (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl)).comp
      ((Abelianization.of).comp
        (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom) =
      (Abelianization.of).comp
        (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range.subtype := by
    refine MonoidHom.ext fun h => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Abelianization.map_of,
      MonoidHom.comp_apply, Subgroup.coe_subtype]
    congr 1
    have := congrArg Subtype.val
      ((MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).apply_symm_apply h)
    rw [MonoidHom.ofInjective_apply] at this
    exact this
  rw [e]

end Transfer

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}

section General

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_fixedOpen_sylow {p : ℕ} [Fact p.Prime]
    (P : Sylow p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    Function.Surjective (D.reciprocity (le_fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) hax) ∧
      (D.reciprocity (le_fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) hax).ker ≤
        commutator (((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G) ⧸
          (L : Subgroup G).subgroupOf ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G)) :=
  reciprocity_of_isPGroup hax _ (le_fixedOpen hLK _) rfl
    (P.isPGroup'.of_equiv (galFixedEquiv hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))).symm)

theorem reciprocity_surjective : Function.Surjective (D.reciprocity hLK hax) := by
  classical
  intro x
  by_contra hx
  set R := (D.reciprocity hLK hax).range with hR
  have hxR : x ∉ R := fun h => hx (MonoidHom.mem_range.1 h)
  set y : tateZero A (K : Subgroup G) (L : Subgroup G) ⧸ R := (x : _ ⧸ R) with hy
  have hy1 : y ≠ 1 := fun h => hxR ((QuotientGroup.eq_one_iff x).1 h)
  obtain ⟨p, hp, hpy⟩ := Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.1 hy1)
  have := Fact.mk hp
  let P : Sylow p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := Classical.arbitrary _
  have hMK : ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G) ≤ K :=
    fun _ h => fixedOpen_le hLK _ h
  obtain ⟨hs, -⟩ := reciprocity_fixedOpen_sylow (D := D) hLK hax P

  have hyP : y ^ (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)).index = 1 := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨t, ht⟩ := hs ((⟨a, fixedModule_anti hMK a.2⟩ :
      fixedModule A ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G)) :
        tateZero A _ (L : Subgroup G))
    have e := D.reciprocity_galRestrict hax hLK (le_fixedOpen hLK _) (fixedOpen_le hLK _) le_rfl t
    rw [ht, normTateZero_mk] at e
    have hn : norm A (K : Subgroup G) ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G)
        ⟨a, fixedModule_anti hMK a.2⟩ = a ^ (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)).index := by
      apply Subtype.ext
      rw [coe_norm_of_mem hMK a.2, relIndex_fixedOpen_eq_index, SubgroupClass.coe_pow]
    rw [hn, QuotientGroup.mk_pow] at e
    rw [hy, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨_, e⟩
  exact Sylow.not_dvd_index P (hpy.trans (orderOf_dvd_of_pow_eq_one hyP))

theorem ker_reciprocity_le_commutator :
    (D.reciprocity hLK hax).ker ≤ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  classical
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  by_contra h1
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.1 h1)
  have := Fact.mk hp
  let P : Sylow p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := Classical.arbitrary _
  obtain ⟨-, hk⟩ := reciprocity_fixedOpen_sylow (D := D) hLK hax P
  have hinj := Abelianization.lift_injective_of_ker_le _ hk
  have hv := D.reciprocity_verlagerung hax (le_fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)))
    (fixedOpen_le hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) σ
  rw [hσ, map_one] at hv
  have hv1 : verlagerung (L := L) (fixedOpen_le hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) σ = 1 :=
    hinj (by rw [hv, map_one])
  have hmap := map_verlagerung (fixedOpen_le hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) σ
  rw [hv1, map_one, range_galRestrict_fixedOpen] at hmap
  exact Sylow.not_dvd_index P (hpd.trans (orderOf_dvd_of_pow_eq_one hmap.symm))

theorem ker_reciprocity_eq_commutator :
    (D.reciprocity hLK hax).ker = commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  refine le_antisymm (ker_reciprocity_le_commutator hLK hax) ?_
  rw [← Abelianization.ker_of]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  rw [← Abelianization.lift_apply_of (D.reciprocity hLK hax), hσ, map_one]

variable (D) in

noncomputable def reciprocityAb :
    Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) →*
      tateZero A (K : Subgroup G) (L : Subgroup G) :=
  Abelianization.lift (D.reciprocity hLK hax)

theorem reciprocityAb_of (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    D.reciprocityAb hLK hax (Abelianization.of q) = D.reciprocity hLK hax q :=
  Abelianization.lift_apply_of _ q

theorem reciprocityAb_bijective : Function.Bijective (D.reciprocityAb hLK hax) := by
  refine ⟨Abelianization.lift_injective_of_ker_le _ (ker_reciprocity_le_commutator hLK hax),
    fun x => ?_⟩
  obtain ⟨q, hq⟩ := reciprocity_surjective (D := D) hLK hax x
  exact ⟨Abelianization.of q, hq⟩

variable (D) in

noncomputable def reciprocityAbEquiv :
    Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ≃*
      tateZero A (K : Subgroup G) (L : Subgroup G) :=
  MulEquiv.ofBijective _ (reciprocityAb_bijective (D := D) hLK hax)

theorem reciprocityAbEquiv_apply (z : Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    D.reciprocityAbEquiv hLK hax z = D.reciprocityAb hLK hax z :=
  rfl

theorem reciprocityAbEquiv_of (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    D.reciprocityAbEquiv hLK hax (Abelianization.of q) = D.reciprocity hLK hax q :=
  reciprocityAb_of hLK hax q

include hLK hax in

theorem card_tateZero (D : ClassFieldData G A) :
    Nat.card (tateZero A (K : Subgroup G) (L : Subgroup G)) =
      Nat.card (Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :=
  (Nat.card_congr (D.reciprocityAbEquiv hLK hax).toEquiv).symm

theorem reciprocity_bijective_of_isMulCommutative
    [IsMulCommutative ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)] :
    Function.Bijective (D.reciprocity hLK hax) := by
  refine ⟨?_, reciprocity_surjective hLK hax⟩
  rw [injective_iff_map_eq_one]
  intro q hq
  have h := ker_reciprocity_le_commutator (D := D) hLK hax hq
  rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer.2 (fun x _ y _ => mul_comm' y x)] at h
  exact h

end General

section Squares

variable (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocityAb_map_galRestrict {K L K' L' : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (hL'K' : L' ≤ K')
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L)
    (z : Abelianization ((K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K')) :
    D.reciprocityAb hLK hax (Abelianization.map (galRestrict hK hL) z) =
      normTateZero hK hL hL'K' hLK (D.reciprocityAb hL'K' hax z) := by
  induction z using QuotientGroup.induction_on with
  | H q =>
    show D.reciprocityAb hLK hax (Abelianization.map (galRestrict hK hL) (Abelianization.of q)) =
      normTateZero hK hL hL'K' hLK (D.reciprocityAb hL'K' hax (Abelianization.of q))
    rw [Abelianization.map_of, reciprocityAb_of, reciprocityAb_of,
      D.reciprocity_galRestrict hax hLK hL'K' hK hL q]

theorem reciprocityAbEquiv_symm_normTateZero {K L K' L' : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (hL'K' : L' ≤ K')
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L)
    (x : tateZero A (K' : Subgroup G) (L' : Subgroup G)) :
    (D.reciprocityAbEquiv hLK hax).symm (normTateZero hK hL hL'K' hLK x) =
      Abelianization.map (galRestrict hK hL) ((D.reciprocityAbEquiv hL'K' hax).symm x) := by
  rw [MulEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (D.reciprocityAbEquiv hL'K' hax).surjective x
  rw [MulEquiv.symm_apply_apply, reciprocityAbEquiv_apply, reciprocityAbEquiv_apply,
    reciprocityAb_map_galRestrict]

theorem reciprocityAbEquiv_symm_tateZeroConj (σ : G) {K L : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (x : tateZero A (K : Subgroup G) (L : Subgroup G)) :
    (D.reciprocityAbEquiv (conjOpen_mono σ hLK) hax).symm (tateZeroConj σ K L x) =
      Abelianization.map (galConj σ K L) ((D.reciprocityAbEquiv hLK hax).symm x) := by
  rw [MulEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (D.reciprocityAbEquiv hLK hax).surjective x
  rw [MulEquiv.symm_apply_apply]
  induction z using QuotientGroup.induction_on with
  | H q =>
    show tateZeroConj σ K L (D.reciprocityAbEquiv hLK hax (Abelianization.of q)) =
      D.reciprocityAbEquiv (conjOpen_mono σ hLK) hax
        (Abelianization.map (galConj σ K L) (Abelianization.of q))
    rw [Abelianization.map_of, reciprocityAbEquiv_of, reciprocityAbEquiv_of,
      D.reciprocity_galConj hax σ hLK q]

theorem reciprocityAbEquiv_symm_tateZeroIncl {K K' L : OpenSubgroup G}
    [((L : Subgroup G).subgroupOf K).Normal] [((L : Subgroup G).subgroupOf K').Normal]
    (hLK' : L ≤ K') (hK'K : K' ≤ K) (x : tateZero A (K : Subgroup G) (L : Subgroup G)) :
    (D.reciprocityAbEquiv hLK' hax).symm (tateZeroIncl hLK' hK'K x) =
      Abelianization.lift (verlagerung hK'K) ((D.reciprocityAbEquiv (hLK'.trans hK'K) hax).symm x) := by
  rw [MulEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (D.reciprocityAbEquiv (hLK'.trans hK'K) hax).surjective x
  rw [MulEquiv.symm_apply_apply]
  induction z using QuotientGroup.induction_on with
  | H q =>
    show tateZeroIncl hLK' hK'K (D.reciprocityAbEquiv (hLK'.trans hK'K) hax (Abelianization.of q)) =
      D.reciprocityAbEquiv hLK' hax (Abelianization.lift (verlagerung hK'K) (Abelianization.of q))
    rw [Abelianization.lift_apply_of, reciprocityAbEquiv_of, reciprocityAbEquiv_apply, reciprocityAb,
      D.reciprocity_verlagerung hax hLK' hK'K q]

end Squares

section Unramified

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocityAbEquiv_symm_of_unramified (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1)
    (a : fixedModule A (K : Subgroup G)) :
    (D.reciprocityAbEquiv hLK hax).symm (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      Abelianization.of (φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^
        (proj (D.relInertiaDegreePNat hLK) (Multiplicative.toAdd (D.valuation K a))).val := by
  obtain ⟨π, hπ⟩ := D.exists_prime K
  rw [MulEquiv.symm_apply_eq, map_pow, reciprocityAbEquiv_of,
    reciprocity_frobenius_of_unramified hLK hax hu hφ hπ]
  apply (D.tateZeroVal_bijective hax hLK hu).1
  rw [map_pow, tateZeroVal_mk, tateZeroVal_mk, valuationMod_apply, valuationMod_apply, hπ, toAdd_ofAdd,
    map_one, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]

theorem reciprocityAbEquiv_symm_of_unramified_of_valuation (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1)
    (a : fixedModule A (K : Subgroup G)) (m : ℤ)
    (ha : D.valuation K a = Multiplicative.ofAdd (m : ℤ̂)) :
    (D.reciprocityAbEquiv hLK hax).symm (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      Abelianization.of (φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ m := by
  obtain ⟨π, hπ⟩ := D.exists_prime K
  rw [MulEquiv.symm_apply_eq, map_zpow, reciprocityAbEquiv_of,
    reciprocity_frobenius_of_unramified hLK hax hu hφ hπ]
  apply (D.tateZeroVal_bijective hax hLK hu).1
  rw [map_zpow, tateZeroVal_mk, tateZeroVal_mk, valuationMod_apply, valuationMod_apply, hπ, ha,
    toAdd_ofAdd, toAdd_ofAdd, map_one, map_intCast, ← ofAdd_zsmul, zsmul_one]

end Unramified

end ClassFieldData

end GroundTheory.LocalField.Abstract
