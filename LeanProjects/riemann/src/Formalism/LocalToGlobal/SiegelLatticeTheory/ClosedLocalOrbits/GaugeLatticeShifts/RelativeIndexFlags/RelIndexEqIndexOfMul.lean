import Mathlib

namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

variable {G : Type*} [Group G]

theorem relIndex_eq_index_of_mul (A R : Subgroup G)
    (h : ∀ y : G, ∃ r ∈ R, ∃ a ∈ A, y = r * a) : A.relIndex R = A.index := by
  have hs : MulAction.stabilizer R (((1 : G) : G ⧸ A)) = A.subgroupOf R := by
    ext r
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change ((((r : G) * 1 : G)) : G ⧸ A) = ((1 : G) : G ⧸ A) ↔ _
    rw [mul_one, QuotientGroup.eq]
    simp
  have ho : MulAction.orbit R (((1 : G) : G ⧸ A)) = Set.univ := by
    ext q
    simp only [Set.mem_univ, iff_true]
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨r, hr, a, ha, rfl⟩ := h y
      refine ⟨⟨r, hr⟩, ?_⟩
      change ((((r : G) * 1 : G)) : G ⧸ A) = ((r * a : G) : G ⧸ A)
      rw [mul_one, QuotientGroup.eq]
      simpa using ha
  rw [Subgroup.relIndex, ← hs, MulAction.index_stabilizer, ho, Set.ncard_univ,
    Subgroup.index_eq_card]

theorem relIndex_eq_of_mul (A B B' : Subgroup G) (hBB : B ≤ B')
    (h : ∀ y ∈ B', ∃ b ∈ B, ∃ a ∈ A, y = b * a) : A.relIndex B = A.relIndex B' := by
  rw [← Subgroup.relIndex_subgroupOf hBB]
  refine relIndex_eq_index_of_mul (A.subgroupOf B') (B.subgroupOf B') ?_
  intro y
  obtain ⟨b, hb, a, ha, hy⟩ := h y.1 y.2
  have haB : a ∈ B' := by
    have : a = b⁻¹ * y.1 := by rw [hy]; group
    rw [this]; exact B'.mul_mem (B'.inv_mem (hBB hb)) y.2
  refine ⟨⟨b, hBB hb⟩, ?_, ⟨a, haB⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]; exact hb
  · rw [Subgroup.mem_subgroupOf]; exact ha
  · apply Subtype.ext; simp [hy]

theorem inf_relIndex_of_le (H N L : Subgroup G) (hL : L ≤ N) :
    (H ⊓ N).relIndex L = H.relIndex L := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hL x.2⟩⟩

theorem relIndex_split (N : Subgroup G) [hN : N.Normal] (H X : Subgroup G) (hHX : H ≤ X) :
    H.relIndex X = (H ⊓ N).relIndex (X ⊓ N) * (H ⊔ N).relIndex (X ⊔ N) := by
  have e1 := Subgroup.relIndex_inf_mul_relIndex H (H ⊔ N) X
  rw [show H ⊓ (H ⊔ N) = H from inf_of_le_left le_sup_left] at e1
  have e2 : (H ⊔ N).relIndex X = (H ⊔ N).relIndex (X ⊔ N) := by
    refine relIndex_eq_of_mul _ _ _ le_sup_left ?_
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := (Subgroup.mem_sup_of_normal_right).1 hy
    exact ⟨x, hx, z, Subgroup.mem_sup_right hz, rfl⟩
  have e3 : H.relIndex (X ⊓ N) = H.relIndex ((H ⊔ N) ⊓ X) := by
    refine relIndex_eq_of_mul _ _ _ ?_ ?_
    · intro y hy
      exact ⟨Subgroup.mem_sup_right hy.2, hy.1⟩
    · intro y hy
      obtain ⟨h, hh, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right).1 hy.1
      refine ⟨y * h⁻¹, ⟨X.mul_mem hy.2 (X.inv_mem (hHX hh)), ?_⟩, h, hh, by group⟩
      rw [← hyz]
      have : h * z * h⁻¹ ∈ N := hN.conj_mem z hz h
      simpa [mul_assoc] using this
  rw [← e1, ← e3, e2, inf_relIndex_of_le H N (X ⊓ N) inf_le_right]

abbrev cj (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom

theorem mem_cj (g : G) (A : Subgroup G) (y : G) : y ∈ cj g A ↔ ∃ x ∈ A, g * x * g⁻¹ = y := by
  simp [cj, Subgroup.mem_map, MulAut.conj_apply]

end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
