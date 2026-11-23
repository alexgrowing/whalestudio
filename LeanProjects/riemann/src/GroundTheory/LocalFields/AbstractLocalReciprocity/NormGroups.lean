import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.Isomorphism

namespace GroundTheory.LocalField.Abstract

section Abelian

variable {G : Type*} [Group G] [TopologicalSpace G]

def IsAbelianExtension (K L : OpenSubgroup G) : Prop :=
  L ≤ K ∧ commutator (K : Subgroup G) ≤ (L : Subgroup G).subgroupOf K

variable {K L : OpenSubgroup G}

theorem IsAbelianExtension.le (h : IsAbelianExtension K L) : L ≤ K :=
  h.1

theorem IsAbelianExtension.commutator_le (h : IsAbelianExtension K L) :
    commutator (K : Subgroup G) ≤ (L : Subgroup G).subgroupOf K :=
  h.2

theorem IsAbelianExtension.normal (h : IsAbelianExtension K L) :
    ((L : Subgroup G).subgroupOf K).Normal :=
  Subgroup.Normal.of_commutator_le _ h.2

theorem IsAbelianExtension.isMulCommutative (h : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    IsMulCommutative ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2 h.2

theorem isAbelianExtension_of_isMulCommutative (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    [IsMulCommutative ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)] : IsAbelianExtension K L :=
  ⟨hLK, Subgroup.Normal.quotient_commutative_iff_commutator_le.1 inferInstance⟩

theorem IsAbelianExtension.mono {H : OpenSubgroup G} (h : IsAbelianExtension K L) (hLH : L ≤ H)
    (hHK : H ≤ K) : IsAbelianExtension K H :=
  ⟨hHK, fun _ hx => hLH (h.2 hx)⟩

theorem IsAbelianExtension.inf {L' : OpenSubgroup G} (h : IsAbelianExtension K L)
    (h' : IsAbelianExtension K L') : IsAbelianExtension K (L ⊓ L') :=
  ⟨inf_le_left.trans h.le, fun _ hx => ⟨h.2 hx, h'.2 hx⟩⟩

theorem isAbelianExtension_self (K : OpenSubgroup G) : IsAbelianExtension K K :=
  ⟨le_rfl, fun x _ => x.2⟩

variable [IsTopologicalGroup G]

def maxAbelian (hLK : L ≤ K) : OpenSubgroup G where
  toSubgroup :=
    ((L : Subgroup G).subgroupOf K ⊔ commutator (K : Subgroup G)).map (K : Subgroup G).subtype
  isOpen' := Subgroup.isOpen_mono (H₁ := (L : Subgroup G))
    (fun x hx => ⟨⟨x, hLK hx⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hx), rfl⟩) L.isOpen

theorem mem_maxAbelian (hLK : L ≤ K) (x : (K : Subgroup G)) :
    (x : G) ∈ (maxAbelian hLK : Subgroup G) ↔
      x ∈ (L : Subgroup G).subgroupOf K ⊔ commutator (K : Subgroup G) :=
  Subgroup.mem_map_iff_mem Subtype.val_injective

theorem maxAbelian_le (hLK : L ≤ K) : maxAbelian hLK ≤ K :=
  fun _ ⟨x, _, hx⟩ => hx ▸ x.2

theorem le_maxAbelian (hLK : L ≤ K) : L ≤ maxAbelian hLK :=
  fun x hx => ⟨⟨x, hLK hx⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem isAbelianExtension_maxAbelian (hLK : L ≤ K) : IsAbelianExtension K (maxAbelian hLK) :=
  ⟨maxAbelian_le hLK, fun x hx => (mem_maxAbelian hLK x).2 (Subgroup.mem_sup_right hx)⟩

end Abelian

section NormGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (A : Type*) [CommGroup A] [MulDistribMulAction G A]

noncomputable def normGroup (K L : OpenSubgroup G) : Subgroup (fixedModule A (K : Subgroup G)) :=
  (norm A (K : Subgroup G) (L : Subgroup G)).range

variable {A}

theorem normGroup_mono {K L H : OpenSubgroup G} (hLH : L ≤ H) (hHK : H ≤ K) :
    normGroup A K L ≤ normGroup A K H :=
  range_norm_le_range_norm hLH hHK

end NormGroup

theorem exists_openSubgroup_normal_le {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (L : OpenSubgroup G) :
    ∃ N : OpenSubgroup G, N ≤ L ∧ (N : Subgroup G).Normal := by
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one L.isOpen L.one_mem
  exact ⟨U.toOpenSubgroup, fun x hx => hU hx, U.isNormal'⟩

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A) (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

section Reciprocity

variable {K L : OpenSubgroup G}

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem mk_eq_one_iff [((L : Subgroup G).subgroupOf K).Normal] (x : (K : Subgroup G)) :
    (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = 1 ↔ (x : G) ∈ (L : Subgroup G) :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf

theorem exists_reciprocity_mk_eq (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (a : fixedModule A (K : Subgroup G)) :
    ∃ x : (K : Subgroup G),
      D.reciprocity hLK hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  obtain ⟨q, hq⟩ := reciprocity_surjective (D := D) hLK hax
    (a : tateZero A (K : Subgroup G) (L : Subgroup G))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨x, hq⟩

theorem reciprocity_mk_of_le {L' : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (hL'K : L' ≤ K) [((L' : Subgroup G).subgroupOf K).Normal]
    (hLL' : L ≤ L') (x : (K : Subgroup G)) (a : fixedModule A (K : Subgroup G))
    (h : D.reciprocity hLK hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    D.reciprocity hL'K hax (x : (K : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L' : Subgroup G)) := by
  have e := D.reciprocity_galRestrict hax hL'K hLK le_rfl hLL'
    (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)
  rw [galRestrict_mk, h, normTateZero_mk, norm_self] at e
  exact e

theorem reciprocity_injective (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] : Function.Injective (D.reciprocity hL.le hax) :=
  haveI := hL.isMulCommutative
  (reciprocity_bijective_of_isMulCommutative (D := D) hL.le hax).1

theorem reciprocity_mk_eq_one_iff (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] (x : (K : Subgroup G)) :
    D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = 1 ↔
      (x : G) ∈ (L : Subgroup G) := by
  rw [← mk_eq_one_iff, ← (D.reciprocity_injective hax hL).eq_iff, map_one]

theorem mem_normGroup_iff_of_reciprocity (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] {x : (K : Subgroup G)}
    {a : fixedModule A (K : Subgroup G)}
    (h : D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    a ∈ normGroup A K L ↔ (x : G) ∈ (L : Subgroup G) := by
  rw [← D.reciprocity_mk_eq_one_iff hax hL, h, QuotientGroup.eq_one_iff]
  rfl

end Reciprocity

section Limitation

variable {K L : OpenSubgroup G}

include D hax

theorem normGroup_maxAbelian (hLK : L ≤ K) :
    normGroup A K (maxAbelian hLK) = normGroup A K L := by
  refine le_antisymm ?_ (normGroup_mono (le_maxAbelian hLK) (maxAbelian_le hLK))
  obtain ⟨N, hNL, hN⟩ := exists_openSubgroup_normal_le L
  have hNK : N ≤ K := hNL.trans hLK
  have hM := isAbelianExtension_maxAbelian hLK
  have := hM.normal
  have := hN
  rintro a ⟨m, rfl⟩
  obtain ⟨x, hx⟩ := D.exists_reciprocity_mk_eq hax hNK
    (norm A (K : Subgroup G) (maxAbelian hLK : Subgroup G) m)
  have hxM : (x : G) ∈ (maxAbelian hLK : Subgroup G) :=
    (D.mem_normGroup_iff_of_reciprocity hax hM
      (D.reciprocity_mk_of_le hax hNK hM.le (hNL.trans (le_maxAbelian hLK)) x _ hx)).1 ⟨m, rfl⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ((mem_maxAbelian hLK x).1 hxM)

  have hz1 : D.reciprocity hNK hax (z : (K : Subgroup G) ⧸ (N : Subgroup G).subgroupOf K) = 1 :=
    MonoidHom.mem_ker.1
      (Abelianization.commutator_subset_ker ((D.reciprocity hNK hax).comp (QuotientGroup.mk' _)) hz)

  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (D.reciprocity hNL hax
    ((⟨y, hy⟩ : (L : Subgroup G)) : (L : Subgroup G) ⧸ (N : Subgroup G).subgroupOf L))
  have e := D.reciprocity_galRestrict hax hNK hNL hLK le_rfl
    ((⟨y, hy⟩ : (L : Subgroup G)) : (L : Subgroup G) ⧸ (N : Subgroup G).subgroupOf L)
  rw [galRestrict_mk, ← hb, normTateZero_mk] at e
  have e' : D.reciprocity hNK hax (y : (K : Subgroup G) ⧸ (N : Subgroup G).subgroupOf K) =
      (norm A (K : Subgroup G) (L : Subgroup G) b : tateZero A (K : Subgroup G) (N : Subgroup G)) := e
  rw [QuotientGroup.mk_mul, map_mul, hz1, mul_one, e'] at hx
  obtain ⟨c, hc⟩ := QuotientGroup.eq.1 hx
  refine ⟨b * norm A (L : Subgroup G) (N : Subgroup G) c, ?_⟩
  rw [map_mul, norm_norm hNL hLK, hc, mul_inv_cancel_left]

end Limitation

section Correspondence

variable {K L L' : OpenSubgroup G}

include D hax

theorem normGroup_le_normGroup_iff (hL : IsAbelianExtension K L) (hL' : IsAbelianExtension K L') :
    normGroup A K L ≤ normGroup A K L' ↔ L ≤ L' := by
  refine ⟨fun h => ?_, fun h => normGroup_mono h hL'.le⟩
  have hI := hL.inf hL'
  have := hI.normal
  have := hL.normal
  have := hL'.normal
  intro g hg
  have hgK : g ∈ (K : Subgroup G) := hL.le hg
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (D.reciprocity hI.le hax
    ((⟨g, hgK⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ ((L ⊓ L' : OpenSubgroup G) : Subgroup G).subgroupOf K))
  have h1 := D.reciprocity_mk_of_le hax hI.le hL.le inf_le_left ⟨g, hgK⟩ a ha.symm
  have h2 := D.reciprocity_mk_of_le hax hI.le hL'.le inf_le_right ⟨g, hgK⟩ a ha.symm
  exact (D.mem_normGroup_iff_of_reciprocity hax hL' h2).1
    (h ((D.mem_normGroup_iff_of_reciprocity hax hL h1).2 hg))

theorem normGroup_eq_normGroup_iff (hL : IsAbelianExtension K L) (hL' : IsAbelianExtension K L') :
    normGroup A K L = normGroup A K L' ↔ L = L' := by
  rw [le_antisymm_iff, le_antisymm_iff, D.normGroup_le_normGroup_iff hax hL hL',
    D.normGroup_le_normGroup_iff hax hL' hL]

theorem normGroup_injective (K : OpenSubgroup G) :
    Function.Injective fun L : {L : OpenSubgroup G // IsAbelianExtension K L} => normGroup A K L :=
  fun L L' h => Subtype.ext ((D.normGroup_eq_normGroup_iff hax L.2 L'.2).1 h)

theorem exists_normGroup_eq_of_le_of_isAbelianExtension (hL : IsAbelianExtension K L)
    {B : Subgroup (fixedModule A (K : Subgroup G))} (hB : normGroup A K L ≤ B) :
    ∃ H : OpenSubgroup G, IsAbelianExtension K H ∧ L ≤ H ∧ normGroup A K H = B := by
  have := hL.normal
  set Q : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
    (B.map (QuotientGroup.mk' (norm A (K : Subgroup G) (L : Subgroup G)).range)).comap
      (D.reciprocity hL.le hax) with hQ
  have hH : IsAbelianExtension K (fixedOpen hL.le Q) :=
    hL.mono (le_fixedOpen hL.le Q) (fixedOpen_le hL.le Q)
  have := hH.normal
  refine ⟨fixedOpen hL.le Q, hH, le_fixedOpen hL.le Q, ?_⟩
  ext a
  obtain ⟨x, hx⟩ := D.exists_reciprocity_mk_eq hax hL.le a
  rw [D.mem_normGroup_iff_of_reciprocity hax hH
    (D.reciprocity_mk_of_le hax hL.le hH.le (le_fixedOpen hL.le Q) x a hx), mem_fixedOpen]
  constructor
  · rintro ⟨_, hq⟩
    have hq' : D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈
        B.map (QuotientGroup.mk' (norm A (K : Subgroup G) (L : Subgroup G)).range) := hq
    rw [hx] at hq'
    obtain ⟨b, hbB, hba⟩ := Subgroup.mem_map.1 hq'
    obtain ⟨n, hn⟩ := QuotientGroup.eq.1 hba
    have ha : a = b * (b⁻¹ * a) := (mul_inv_cancel_left b a).symm
    rw [ha, ← hn]
    exact B.mul_mem hbB (hB ⟨n, rfl⟩)
  · intro ha
    refine ⟨x.2, ?_⟩
    show D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈
      B.map (QuotientGroup.mk' (norm A (K : Subgroup G) (L : Subgroup G)).range)
    rw [hx]
    exact ⟨a, ha, rfl⟩

theorem exists_normGroup_eq_of_le (hLK : L ≤ K) {B : Subgroup (fixedModule A (K : Subgroup G))}
    (hB : normGroup A K L ≤ B) :
    ∃ H : OpenSubgroup G, IsAbelianExtension K H ∧ L ≤ H ∧ normGroup A K H = B := by
  rw [← D.normGroup_maxAbelian hax hLK] at hB
  obtain ⟨H, hH, hMH, e⟩ :=
    D.exists_normGroup_eq_of_le_of_isAbelianExtension hax (isAbelianExtension_maxAbelian hLK) hB
  exact ⟨H, hH, (le_maxAbelian hLK).trans hMH, e⟩

theorem index_normGroup (hL : IsAbelianExtension K L) :
    (normGroup A K L).index = (L : Subgroup G).relIndex K := by
  have := hL.normal
  have := hL.isMulCommutative
  rw [Subgroup.index_eq_card, ← card_quotient_eq_relIndex]
  exact (Nat.card_congr
    (Equiv.ofBijective _ (reciprocity_bijective_of_isMulCommutative (D := D) hL.le hax))).symm

end Correspondence

end ClassFieldData

end GroundTheory.LocalField.Abstract
