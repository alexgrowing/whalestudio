import Mathlib

noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology MeasureTheory
open scoped Pointwise

section Space

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X]

theorem exists_isCompact_isOpen_subset {x : X} {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ V : Set X, IsCompact V ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds hU
  obtain ⟨V, hV, hxV, hVK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK
  exact ⟨V, hKc.of_isClosed_subset hV.isClosed hVK, hV.isOpen, hxV, hVK.trans hKU⟩

end Space

section VanDantzig

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem exists_openSubgroup_isCompact_subset {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨W, hWc, hWo, h1W, hWU⟩ := exists_isCompact_isOpen_subset hU
  obtain ⟨V, hV1, hWV⟩ := compact_open_separated_mul_right hWc hWo subset_rfl

  let H : Subgroup G :=
    { carrier := {x | ∀ w, w ∈ W ↔ w * x ∈ W}
      one_mem' := fun w => by simp
      mul_mem' := fun {a b} ha hb w => by rw [ha w, hb (w * a), mul_assoc]
      inv_mem' := fun {a} ha w => by
        have := ha (w * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  have hVH : V ∩ V⁻¹ ⊆ (H : Set G) := by
    rintro v ⟨hv, hv'⟩ w
    refine ⟨fun hw => hWV (Set.mul_mem_mul hw hv), fun hw => ?_⟩
    have := hWV (Set.mul_mem_mul hw (Set.mem_inv.1 hv'))
    rwa [mul_inv_cancel_right] at this
  have hHn : (H : Set G) ∈ 𝓝 (1 : G) :=
    mem_of_superset (inter_mem hV1 (inv_mem_nhds_one G hV1)) hVH
  have hHW : (H : Set G) ⊆ W := fun x hx => by
    have := (hx 1).1 h1W
    rwa [one_mul] at this
  let K : OpenSubgroup G := ⟨H, H.isOpen_of_mem_nhds hHn⟩
  exact ⟨K, hWc.of_isClosed_subset K.isClosed hHW, hHW.trans hWU⟩

theorem hasBasis_nhds_one_compactOpenSubgroup :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G => IsCompact (K : Set G))
      (fun K => (K : Set G)) :=
  ⟨fun _ => ⟨fun hU => exists_openSubgroup_isCompact_subset hU,
    fun ⟨K, _, hKU⟩ => mem_of_superset K.mem_nhds_one hKU⟩⟩

theorem hasBasis_nhds_compactOpenSubgroup (g : G) :
    (𝓝 g).HasBasis (fun K : OpenSubgroup G => IsCompact (K : Set G))
      (fun K => g • (K : Set G)) := by
  rw [← map_mul_left_nhds_one g]
  convert (hasBasis_nhds_one_compactOpenSubgroup (G := G)).map (g * ·) using 2 with K
  ext x
  simp only [Set.mem_smul_set, smul_eq_mul, Set.mem_image]

theorem exists_compactOpenSubgroup : ∃ K : OpenSubgroup G, IsCompact (K : Set G) := by
  obtain ⟨K, hK, -⟩ := exists_openSubgroup_isCompact_subset (univ_mem : univ ∈ 𝓝 (1 : G))
  exact ⟨K, hK⟩

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem isCompact_inf_left {K L : OpenSubgroup G} (hK : IsCompact (K : Set G)) :
    IsCompact ((K ⊓ L : OpenSubgroup G) : Set G) := by
  rw [OpenSubgroup.coe_inf]
  exact hK.inter_right L.isClosed

theorem exists_compactOpenSubgroup_normalized {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ N : OpenSubgroup G, IsCompact (N : Set G) ∧ (N : Set G) ⊆ U ∧
      ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
  obtain ⟨L, hLc, hLU⟩ := exists_openSubgroup_isCompact_subset hU

  have hopen : IsOpen ((fun p : G × G => p.1 * p.2 * p.1⁻¹) ⁻¹' (L : Set G)) :=
    L.isOpen.preimage (by fun_prop)
  have hsub : (K : Set G) ×ˢ ({1} : Set G) ⊆
      (fun p : G × G => p.1 * p.2 * p.1⁻¹) ⁻¹' (L : Set G) := by
    rintro ⟨k, x⟩ ⟨-, hx⟩
    simp only [mem_singleton_iff] at hx
    simp [hx]
  obtain ⟨u, v, -, hv, hKu, h1v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hopen hsub

  let N₀ : Subgroup G :=
    { carrier := {x | ∀ k ∈ K, k * x * k⁻¹ ∈ L}
      one_mem' := fun k _ => by simp
      mul_mem' := fun {a b} ha hb k hk => by
        have := mul_mem (ha k hk) (hb k hk)
        simpa [mul_assoc] using this
      inv_mem' := fun {a} ha k hk => by
        have := inv_mem (ha k hk)
        simpa [mul_assoc] using this }
  have hvN : v ⊆ (N₀ : Set G) := fun x hx k hk =>
    huv (show (k, x) ∈ u ×ˢ v from ⟨hKu hk, hx⟩)
  have hN₀n : (N₀ : Set G) ∈ 𝓝 (1 : G) := mem_of_superset (hv.mem_nhds (h1v rfl)) hvN
  have hN₀L : (N₀ : Set G) ⊆ L := fun x hx => by simpa using hx 1 K.one_mem
  let N : OpenSubgroup G := ⟨N₀, N₀.isOpen_of_mem_nhds hN₀n⟩
  refine ⟨N, hLc.of_isClosed_subset N.isClosed hN₀L, hN₀L.trans hLU, fun k hk n hn j hj => ?_⟩
  have := hn (j * k) (mul_mem hj hk)
  simpa [mul_assoc] using this

end VanDantzig

end GroundTheory.Automorphic
