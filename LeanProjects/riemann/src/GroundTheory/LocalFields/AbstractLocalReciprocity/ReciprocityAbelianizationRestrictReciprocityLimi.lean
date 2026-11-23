import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.NormGroups

namespace GroundTheory.LocalField.Abstract

section Abelianization

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance compactSpace_openSubgroup [CompactSpace G] (K : OpenSubgroup G) :
    CompactSpace (K : Subgroup G) :=
  isCompact_iff_compactSpace.mp K.isClosed.isCompact

variable {K L : OpenSubgroup G}

omit [IsTopologicalGroup G] in

theorem isOpen_subgroupOf (K L : OpenSubgroup G) :
    IsOpen (((L : Subgroup G).subgroupOf K : Subgroup (K : Subgroup G)) : Set (K : Subgroup G)) :=
  L.isOpen.preimage continuous_subtype_val

theorem IsAbelianExtension.topologicalClosure_commutator_le (hL : IsAbelianExtension K L) :
    (commutator (K : Subgroup G)).topologicalClosure ≤ (L : Subgroup G).subgroupOf K :=
  Subgroup.topologicalClosure_minimal _ hL.commutator_le
    (Subgroup.isClosed_of_isOpen _ (isOpen_subgroupOf K L))

noncomputable def abelianizationRestrict (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    TopologicalAbelianization (K : Subgroup G) →* (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K :=
  QuotientGroup.map _ _ (MonoidHom.id _) hL.topologicalClosure_commutator_le

@[simp]
theorem abelianizationRestrict_mk (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] (g : (K : Subgroup G)) :
    abelianizationRestrict hL (g : TopologicalAbelianization (K : Subgroup G)) =
      (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
  rfl

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem mem_topologicalClosure_commutator_iff (x : (K : Subgroup G)) :
    x ∈ (commutator (K : Subgroup G)).topologicalClosure ↔
      ∀ L : OpenSubgroup G, IsAbelianExtension K L → (x : G) ∈ (L : Subgroup G) := by
  refine ⟨fun hx L hL => hL.topologicalClosure_commutator_le hx, fun h => ?_⟩
  have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := (K : Subgroup G))
    ⟨(commutator (K : Subgroup G)).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
  have hx : x ∈ sInf {N : Subgroup (K : Subgroup G) | IsOpen (N : Set (K : Subgroup G)) ∧
      (commutator (K : Subgroup G)).topologicalClosure ≤ N} := by
    rw [Subgroup.mem_sInf]
    rintro N ⟨hNo, hCN⟩
    let M : OpenSubgroup G :=
      { toSubgroup := N.map (K : Subgroup G).subtype
        isOpen' := by
          have h := K.isOpen.isOpenMap_subtype_val _ hNo
          rw [← Subgroup.coe_subtype, ← Subgroup.coe_map] at h
          exact h }
    have hM : IsAbelianExtension K M :=
      ⟨fun _ ⟨y, _, hy⟩ => hy ▸ y.2, fun y hy =>
        ⟨y, hCN (Subgroup.le_topologicalClosure _ hy), rfl⟩⟩
    exact (Subgroup.mem_map_iff_mem Subtype.val_injective).1 (h M hM)
  rw [← key] at hx
  exact hx

end Abelianization

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A) (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

section Equiv

variable {K L : OpenSubgroup G}

noncomputable def reciprocityAbelianEquiv (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K ≃* tateZero A (K : Subgroup G) (L : Subgroup G) :=
  haveI := hL.isMulCommutative
  MulEquiv.ofBijective _ (reciprocity_bijective_of_isMulCommutative (D := D) hL.le hax)

theorem reciprocityAbelianEquiv_apply (hL : IsAbelianExtension K L) [((L : Subgroup G).subgroupOf K).Normal]
    (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    D.reciprocityAbelianEquiv hax hL q = D.reciprocity hL.le hax q :=
  rfl

end Equiv

section Limit

variable (K : OpenSubgroup G)

theorem exists_forall_reciprocity_mk_eq (a : fixedModule A (K : Subgroup G)) :
    ∃ g : (K : Subgroup G), ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L)
      [((L : Subgroup G).subgroupOf K).Normal],
      D.reciprocity hL.le hax (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  let ι := {L : OpenSubgroup G // IsAbelianExtension K L}
  have : Nonempty ι := ⟨⟨K, isAbelianExtension_self K⟩⟩
  let t : ι → Set (K : Subgroup G) := fun L =>
    haveI := L.2.normal
    {g | D.reciprocity L.2.le hax (g : (K : Subgroup G) ⧸ (L.1 : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L.1 : Subgroup G))}
  have htn : ∀ L, (t L).Nonempty := fun L => by
    have := L.2.normal
    obtain ⟨x, hx⟩ := D.exists_reciprocity_mk_eq hax L.2.le a
    exact ⟨x, hx⟩
  have htcl : ∀ L, IsClosed (t L) := fun L => by
    have := L.2.normal
    obtain ⟨x, hx⟩ := htn L
    have ht : t L = (fun g => x⁻¹ * g) ⁻¹'
        (((L.1 : Subgroup G).subgroupOf K : Subgroup (K : Subgroup G)) : Set (K : Subgroup G)) := by
      ext g
      change D.reciprocity L.2.le hax _ = _ ↔ _
      rw [← show D.reciprocity L.2.le hax _ = _ from hx, (D.reciprocity_injective hax L.2).eq_iff,
        eq_comm, QuotientGroup.eq]
      rfl
    rw [ht]
    exact (Subgroup.isClosed_of_isOpen _ (isOpen_subgroupOf K L.1)).preimage
      (continuous_const.mul continuous_id)
  have htd : Directed (· ⊇ ·) t := by
    intro L L'
    refine ⟨⟨L.1 ⊓ L'.1, L.2.inf L'.2⟩, fun g hg => ?_, fun g hg => ?_⟩
    · have := L.2.normal
      have := (L.2.inf L'.2).normal
      exact D.reciprocity_mk_of_le hax (L.2.inf L'.2).le L.2.le inf_le_left g a hg
    · have := L'.2.normal
      have := (L.2.inf L'.2).normal
      exact D.reciprocity_mk_of_le hax (L.2.inf L'.2).le L'.2.le inf_le_right g a hg
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    (fun L => (htcl L).isCompact) htcl
  refine ⟨g, fun L hL _ => ?_⟩
  exact Set.mem_iInter.1 hg ⟨L, hL⟩

theorem mk_eq_mk_of_forall_reciprocity_mk_eq {a : fixedModule A (K : Subgroup G)}
    {g g' : (K : Subgroup G)}
    (hg : ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L) [((L : Subgroup G).subgroupOf K).Normal],
      D.reciprocity hL.le hax (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G)))
    (hg' : ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L) [((L : Subgroup G).subgroupOf K).Normal],
      D.reciprocity hL.le hax (g' : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    (g : TopologicalAbelianization (K : Subgroup G)) = g' := by
  rw [QuotientGroup.eq, mem_topologicalClosure_commutator_iff]
  intro L hL
  have := hL.normal
  have h := (hg L hL).trans (hg' L hL).symm
  rw [(D.reciprocity_injective hax hL).eq_iff, QuotientGroup.eq] at h
  exact h

noncomputable def reciprocityLimit :
    fixedModule A (K : Subgroup G) →* TopologicalAbelianization (K : Subgroup G) where
  toFun a := ((D.exists_forall_reciprocity_mk_eq hax K a).choose :
    TopologicalAbelianization (K : Subgroup G))
  map_one' := by
    rw [← QuotientGroup.mk_one]
    refine D.mk_eq_mk_of_forall_reciprocity_mk_eq hax K
      (D.exists_forall_reciprocity_mk_eq hax K 1).choose_spec ?_
    intro L hL _
    rw [QuotientGroup.mk_one, map_one, QuotientGroup.mk_one]
  map_mul' a b := by
    rw [← QuotientGroup.mk_mul]
    refine D.mk_eq_mk_of_forall_reciprocity_mk_eq hax K
      (D.exists_forall_reciprocity_mk_eq hax K (a * b)).choose_spec ?_
    intro L hL _
    rw [QuotientGroup.mk_mul, map_mul, (D.exists_forall_reciprocity_mk_eq hax K a).choose_spec L hL,
      (D.exists_forall_reciprocity_mk_eq hax K b).choose_spec L hL, QuotientGroup.mk_mul]

variable {K}

theorem reciprocity_abelianizationRestrict_reciprocityLimit {L : OpenSubgroup G}
    (hL : IsAbelianExtension K L) [((L : Subgroup G).subgroupOf K).Normal]
    (a : fixedModule A (K : Subgroup G)) :
    D.reciprocity hL.le hax (abelianizationRestrict hL (D.reciprocityLimit hax K a)) =
      (a : tateZero A (K : Subgroup G) (L : Subgroup G)) :=
  (D.exists_forall_reciprocity_mk_eq hax K a).choose_spec L hL

theorem abelianizationRestrict_reciprocityLimit {L : OpenSubgroup G} (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] (a : fixedModule A (K : Subgroup G)) :
    abelianizationRestrict hL (D.reciprocityLimit hax K a) =
      (D.reciprocityAbelianEquiv hax hL).symm (a : tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  rw [MulEquiv.eq_symm_apply, reciprocityAbelianEquiv_apply,
    D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL]

theorem eq_one_iff_forall_abelianizationRestrict (σ : TopologicalAbelianization (K : Subgroup G)) :
    σ = 1 ↔ ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L)
      [((L : Subgroup G).subgroupOf K).Normal], abelianizationRestrict hL σ = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective σ
  rw [QuotientGroup.eq_one_iff, mem_topologicalClosure_commutator_iff]
  refine ⟨fun h L hL _ => ?_, fun h L hL => ?_⟩
  · rw [abelianizationRestrict_mk, mk_eq_one_iff]
    exact h L hL
  · have := hL.normal
    have h' := h L hL
    rwa [abelianizationRestrict_mk, mk_eq_one_iff] at h'

theorem ext_abelianizationRestrict {σ τ : TopologicalAbelianization (K : Subgroup G)}
    (h : ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L)
      [((L : Subgroup G).subgroupOf K).Normal], abelianizationRestrict hL σ = abelianizationRestrict hL τ) :
    σ = τ := by
  rw [← div_eq_one, eq_one_iff_forall_abelianizationRestrict]
  intro L hL _
  rw [map_div, h L hL, div_self']

theorem eq_reciprocityLimit {a : fixedModule A (K : Subgroup G)}
    {σ : TopologicalAbelianization (K : Subgroup G)}
    (h : ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L)
      [((L : Subgroup G).subgroupOf K).Normal],
      D.reciprocity hL.le hax (abelianizationRestrict hL σ) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    σ = D.reciprocityLimit hax K a := by
  refine ext_abelianizationRestrict fun L hL _ => D.reciprocity_injective hax hL ?_
  rw [h L hL, D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL]

theorem ker_reciprocityLimit :
    (D.reciprocityLimit hax K).ker =
      ⨅ L : {L : OpenSubgroup G // IsAbelianExtension K L}, normGroup A K L.1 := by
  ext a
  rw [MonoidHom.mem_ker, eq_one_iff_forall_abelianizationRestrict, Subgroup.mem_iInf]
  refine ⟨fun h L => ?_, fun h L hL _ => ?_⟩
  · have := L.2.normal
    have h' := congrArg (D.reciprocity L.2.le hax) (h L.1 L.2)
    rw [D.reciprocity_abelianizationRestrict_reciprocityLimit hax L.2, map_one,
      QuotientGroup.eq_one_iff] at h'
    exact h'
  · apply D.reciprocity_injective hax hL
    rw [D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL, map_one,
      QuotientGroup.eq_one_iff]
    exact h ⟨L, hL⟩

theorem ker_reciprocityLimit_eq_iInf :
    (D.reciprocityLimit hax K).ker = ⨅ L : {L : OpenSubgroup G // L ≤ K}, normGroup A K L.1 := by
  rw [ker_reciprocityLimit]
  refine le_antisymm (le_iInf fun L => ?_) (le_iInf fun L => iInf_le_of_le ⟨L.1, L.2.le⟩ le_rfl)
  rw [← D.normGroup_maxAbelian hax L.2]
  exact iInf_le_of_le ⟨maxAbelian L.2, isAbelianExtension_maxAbelian L.2⟩ le_rfl

theorem denseRange_reciprocityLimit : DenseRange (D.reciprocityLimit hax K) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨σ, hσ⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective σ
  set C := (commutator (K : Subgroup G)).topologicalClosure
  set V : Set (K : Subgroup G) := (fun y => ((g * y : (K : Subgroup G)) :
    TopologicalAbelianization (K : Subgroup G))) ⁻¹' U with hV
  have hVo : IsOpen V :=
    hU.preimage (QuotientGroup.continuous_mk.comp (continuous_const.mul continuous_id))
  have hV1 : (1 : (K : Subgroup G)) ∈ V := by
    simp only [hV, Set.mem_preimage, mul_one]
    exact hσ
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVo hV1

  let M : OpenSubgroup G :=
    { toSubgroup := ((N : Subgroup (K : Subgroup G)) ⊔ C).map (K : Subgroup G).subtype
      isOpen' := by
        have ho : IsOpen (((N : Subgroup (K : Subgroup G)) ⊔ C : Subgroup (K : Subgroup G)) :
            Set (K : Subgroup G)) :=
          Subgroup.isOpen_mono (H₁ := (N : Subgroup (K : Subgroup G)))
            (H₂ := (N : Subgroup (K : Subgroup G)) ⊔ C) le_sup_left N.isOpen'
        have h := K.isOpen.isOpenMap_subtype_val _ ho
        rw [← Subgroup.coe_subtype, ← Subgroup.coe_map] at h
        exact h }
  have hMmem : ∀ x : (K : Subgroup G), (x : G) ∈ (M : Subgroup G) ↔ x ∈ (N : Subgroup (K : Subgroup G)) ⊔ C :=
    fun x => Subgroup.mem_map_iff_mem Subtype.val_injective
  have hM : IsAbelianExtension K M :=
    ⟨fun _ ⟨y, _, hy⟩ => hy ▸ y.2, fun y hy =>
      (hMmem y).2 (Subgroup.mem_sup_right (Subgroup.le_topologicalClosure _ hy))⟩
  have := hM.normal
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective
    (D.reciprocity hM.le hax (g : (K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K))
  refine ⟨D.reciprocityLimit hax K a, ?_, a, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (D.reciprocityLimit hax K a)
  have e := D.reciprocity_abelianizationRestrict_reciprocityLimit hax hM a
  rw [← hh, abelianizationRestrict_mk, ha, (D.reciprocity_injective hax hM).eq_iff, eq_comm,
    QuotientGroup.eq] at e

  have e' : g⁻¹ * h ∈ (N : Subgroup (K : Subgroup G)) ⊔ C := (hMmem _).1 e
  obtain ⟨n, hn, c, hc, hnc⟩ := Subgroup.mem_sup_of_normal_left.1 e'
  have hnV : n ∈ V := hN hn
  rw [← hh]
  have hgh : h = g * n * c := by
    rw [mul_assoc, hnc, mul_inv_cancel_left]
  have hmk : ((h : (K : Subgroup G)) : TopologicalAbelianization (K : Subgroup G)) =
      ((g * n : (K : Subgroup G)) : TopologicalAbelianization (K : Subgroup G)) := by
    have hc' : (g * n * c)⁻¹ * (g * n) = c⁻¹ := by group
    rw [QuotientGroup.eq, hgh, hc']
    exact C.inv_mem hc
  rw [hmk]
  exact hnV

end Limit

end ClassFieldData

end GroundTheory.LocalField.Abstract
