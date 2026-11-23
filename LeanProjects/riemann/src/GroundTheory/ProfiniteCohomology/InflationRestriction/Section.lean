import Mathlib
import GroundTheory.ProfiniteCohomology.OpenNormal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cosetSelectors (N : Subgroup G) : Set (Set G) :=
  {T | IsClosed T ∧ ∃ K : Subgroup G, K.Normal ∧ IsClosed (K : Set G) ∧ K ≤ N ∧
    (∀ t ∈ T, ∀ k ∈ K, t * k ∈ T) ∧ (∀ x : G, ∃ t ∈ T, (t : G ⧸ N) = x) ∧
    (∀ t ∈ T, ∀ t' ∈ T, (t : G ⧸ N) = t' → t⁻¹ * t' ∈ K)}

omit [IsTopologicalGroup G] in
theorem univ_mem_cosetSelectors (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    Set.univ ∈ cosetSelectors N :=
  ⟨isClosed_univ, N, inferInstance, hN, le_rfl, fun _ _ _ _ => Set.mem_univ _,
    fun x => ⟨x, Set.mem_univ _, rfl⟩, fun _ _ _ _ h => QuotientGroup.eq.mp h⟩

variable [CompactSpace G]

theorem sInter_mem_cosetSelectors (N : Subgroup G) (hN : IsClosed (N : Set G))
    {c : Set (Set G)} (hcS : c ⊆ cosetSelectors N) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    ⋂₀ c ∈ cosetSelectors N := by
  have : Nonempty c := hne.to_subtype
  choose K hKn hKc hKN hKmul hKex hKuniq using fun T : c => (hcS T.2).2
  refine ⟨isClosed_sInter fun T hT => (hcS hT).1, ⨅ T : c, K T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun n hn g => Subgroup.mem_iInf.2 fun T =>
      (hKn T).conj_mem _ (Subgroup.mem_iInf.1 hn T) g⟩
  · rw [Subgroup.coe_iInf]
    exact isClosed_iInter hKc
  · exact (iInf_le _ (Classical.arbitrary c)).trans (hKN _)
  · intro t ht k hk
    exact Set.mem_sInter.2 fun T hT =>
      hKmul ⟨T, hT⟩ t (Set.mem_sInter.1 ht T hT) k (Subgroup.mem_iInf.1 hk ⟨T, hT⟩)
  · intro x
    have : IsClosed (N : Set G) := hN
    have : T2Space (G ⧸ N) := inferInstance
    have hne' : (⋂ T : c, ((T : Set G) ∩ {t | (t : G ⧸ N) = x})).Nonempty := by
      refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ ?_ ?_ ?_ ?_
      · intro T T'
        rcases hc.total T.2 T'.2 with h | h
        · exact ⟨T, le_rfl, Set.inter_subset_inter_left _ h⟩
        · exact ⟨T', Set.inter_subset_inter_left _ h, le_rfl⟩
      · intro T
        obtain ⟨t, ht, htx⟩ := hKex T x
        exact ⟨t, ht, htx⟩
      · intro T
        exact ((hcS T.2).1.inter (isClosed_eq QuotientGroup.continuous_mk continuous_const)).isCompact
      · intro T
        exact (hcS T.2).1.inter (isClosed_eq QuotientGroup.continuous_mk continuous_const)
    obtain ⟨t, ht⟩ := hne'
    rw [Set.mem_iInter] at ht
    refine ⟨t, Set.mem_sInter.2 fun T hT => (ht ⟨T, hT⟩).1, ?_⟩
    exact (ht (Classical.arbitrary c)).2
  · intro t ht t' ht' h
    exact Subgroup.mem_iInf.2 fun T =>
      hKuniq T t (Set.mem_sInter.1 ht T T.2) t' (Set.mem_sInter.1 ht' T T.2) h

variable [TotallyDisconnectedSpace G]

theorem exists_closed_transversal (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    ∃ T : Set G, IsClosed T ∧ (∀ x : G, ∃ t ∈ T, (t : G ⧸ N) = x) ∧
      ∀ t ∈ T, ∀ t' ∈ T, (t : G ⧸ N) = t' → t = t' := by
  obtain ⟨T, hTmin⟩ := zorn_superset (cosetSelectors N) fun c hcS hc => by
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨Set.univ, univ_mem_cosetSelectors N hN, fun s hs => absurd hs (Set.notMem_empty s)⟩
    · exact ⟨⋂₀ c, sInter_mem_cosetSelectors N hN hcS hc hne, fun s hs => Set.sInter_subset_of_mem hs⟩
  obtain ⟨hTc, K, hKn, hKc, hKN, hKmul, hKex, hKuniq⟩ := hTmin.prop
  suffices hK : ∀ x ∈ K, x = 1 by
    refine ⟨T, hTc, hKex, fun t ht t' ht' h => ?_⟩
    have := hK _ (hKuniq t ht t' ht' h)
    rw [inv_mul_eq_one] at this
    exact this
  intro x hxK
  by_contra hx1

  have hxnhds : ({x}ᶜ : Set G) ∈ 𝓝 (1 : G) :=
    isOpen_compl_singleton.mem_nhds (Ne.symm hx1)
  obtain ⟨U, -, hU⟩ := (OpenNormalSubgroup.hasBasis_nhds_one (G := G)).mem_iff.mp hxnhds
  have hxU : x ∉ (U : Subgroup G) := fun h => hU h rfl
  let W : Subgroup G := K ⊔ (U : Subgroup G)
  have hWopen : IsOpen (W : Set G) :=
    Subgroup.isOpen_mono le_sup_right U.toOpenSubgroup.isOpen
  have : W.Normal := Subgroup.sup_normal K (U : Subgroup G)
  have : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hWopen
  let r : G ⧸ W → G ⧸ (U : Subgroup G) := fun D => ((Quotient.out D : G) : G ⧸ (U : Subgroup G))
  let T' : Set G := T ∩ {g | (g : G ⧸ (U : Subgroup G)) = r (g : G ⧸ W)}
  have hT'c : IsClosed T' :=
    hTc.inter (isClosed_eq QuotientGroup.continuous_mk
      ((continuous_of_discreteTopology (f := r)).comp QuotientGroup.continuous_mk))
  have hK'n : (K ⊓ (U : Subgroup G)).Normal := Subgroup.normal_inf_normal _ _
  have hT'mem : T' ∈ cosetSelectors N := by
    refine ⟨hT'c, K ⊓ (U : Subgroup G), hK'n,
      hKc.inter U.toOpenSubgroup.isClosed, inf_le_left.trans hKN, ?_, ?_, ?_⟩
    · rintro t ⟨ht, htr⟩ k ⟨hkK, hkU⟩
      refine ⟨hKmul t ht k hkK, ?_⟩
      have h1 : ((t * k : G) : G ⧸ (U : Subgroup G)) = (t : G ⧸ (U : Subgroup G)) :=
        QuotientGroup.eq.mpr (by simpa using (U : Subgroup G).inv_mem hkU)
      have h2 : ((t * k : G) : G ⧸ W) = (t : G ⧸ W) :=
        QuotientGroup.eq.mpr (by simpa using W.inv_mem (le_sup_left (b := (U : Subgroup G)) hkK))
      simp only [Set.mem_ofPred_eq] at htr ⊢
      rw [h1, h2]
      exact htr
    · intro y
      obtain ⟨t, ht, hty⟩ := hKex y
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W t
      obtain ⟨k, hk, u, hu, hku⟩ := Subgroup.mem_sup_of_normal_right.mp w.2
      refine ⟨t * k, ⟨hKmul t ht k hk, ?_⟩, ?_⟩
      · simp only [Set.mem_ofPred_eq, r]
        have h2 : ((t * k : G) : G ⧸ W) = (t : G ⧸ W) :=
          QuotientGroup.eq.mpr (by simpa using W.inv_mem (le_sup_left (b := (U : Subgroup G)) hk))
        rw [h2, hw, ← hku, ← mul_assoc]
        exact QuotientGroup.eq.mpr (by convert hu using 1; group)
      · rw [← hty]
        exact QuotientGroup.eq.mpr (by simpa using hKN hk)
    · rintro t ⟨ht, htr⟩ t' ⟨ht', ht'r⟩ h
      have hK1 := hKuniq t ht t' ht' h
      refine ⟨hK1, ?_⟩
      have hW : (t : G ⧸ W) = t' := QuotientGroup.eq.mpr (le_sup_left (b := (U : Subgroup G)) hK1)
      simp only [Set.mem_ofPred_eq] at htr ht'r
      have : (t : G ⧸ (U : Subgroup G)) = t' := by rw [htr, ht'r, hW]
      exact QuotientGroup.eq.mp this
  have hTT' : T ⊆ T' := hTmin.2 hT'mem Set.inter_subset_left
  obtain ⟨t, ht, -⟩ := hKex 1
  have htx : t * x ∈ T := hKmul t ht x hxK

  obtain ⟨t₀, ⟨ht₀, ht₀r⟩, -⟩ := (⟨t, hTT' ht, rfl⟩ : ∃ t₀ ∈ T', t₀ = t)
  have hsame : (t : G ⧸ N) = (t * x : G) := QuotientGroup.eq.mpr (by simpa using hKN hxK)
  have hmem := (hT'mem.2.choose_spec)

  have h1 := (hTT' ht).2
  have h2 := (hTT' htx).2
  have hW : (t : G ⧸ W) = (t * x : G) :=
    QuotientGroup.eq.mpr (by simpa using le_sup_left (b := (U : Subgroup G)) hxK)
  simp only [Set.mem_ofPred_eq] at h1 h2
  have : (t : G ⧸ (U : Subgroup G)) = (t * x : G) := by rw [h1, h2, hW]
  exact hxU (by simpa using QuotientGroup.eq.mp this)

theorem exists_continuous_section (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    ∃ s : G ⧸ N → G, Continuous s ∧ (∀ c, (s c : G ⧸ N) = c) ∧ s 1 = 1 := by
  have : IsClosed (N : Set G) := hN
  have : T2Space (G ⧸ N) := inferInstance
  obtain ⟨T, hTc, hex, huniq⟩ := exists_closed_transversal N hN
  have : CompactSpace T := isCompact_iff_compactSpace.mp hTc.isCompact
  let f : T → G ⧸ N := fun t => (t : G)
  have hf : Function.Bijective f := by
    refine ⟨fun t t' h => Subtype.ext (huniq t t.2 t' t'.2 h), fun c => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨t, ht, htx⟩ := hex x
    exact ⟨⟨t, ht⟩, htx⟩
  let e : T ≃ₜ G ⧸ N := (QuotientGroup.continuous_mk.comp continuous_subtype_val :
    Continuous f).homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
  let s₀ : G ⧸ N → G := fun c => (e.symm c : G)
  have hs₀ : ∀ c, (s₀ c : G ⧸ N) = c := fun c => e.apply_symm_apply c
  have h1 : s₀ 1 ∈ N := by
    have := hs₀ 1
    rw [← QuotientGroup.mk_one, QuotientGroup.eq] at this
    simpa using this
  refine ⟨fun c => s₀ c * (s₀ 1)⁻¹,
    (continuous_subtype_val.comp e.symm.continuous).mul continuous_const, fun c => ?_, ?_⟩
  · calc ((s₀ c * (s₀ 1)⁻¹ : G) : G ⧸ N) = (s₀ c : G ⧸ N) :=
          QuotientGroup.eq.mpr (by convert h1 using 1; group)
      _ = c := hs₀ c
  · exact mul_inv_cancel _

end GroundTheory.ProfCoh
