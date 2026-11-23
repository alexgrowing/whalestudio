import Mathlib
open scoped Pointwise

namespace GlobalTheory.DCIndex

variable {A : Type} [Group A]

theorem normal_of_comm (hc : ∀ a b : A, a * b = b * a) (V : Subgroup A) : V.Normal :=
  ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩

theorem mem_sup_iff (hc : ∀ a b : A, a * b = b * a) (P Q : Subgroup A) {x : A} :
    x ∈ P ⊔ Q ↔ ∃ p ∈ P, ∃ q ∈ Q, p * q = x := by
  haveI : Q.Normal := normal_of_comm hc Q
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem card_quot_eq_index (hc : ∀ a b : A, a * b = b * a) (P V : Subgroup A) :
    Nat.card (DoubleCoset.Quotient (P : Set A) (V : Set A)) = (P ⊔ V).index := by
  rw [Subgroup.index]
  apply Nat.card_congr
  refine Quotient.congr (Equiv.refl A) ?_
  intro x y
  simp only [Equiv.refl_apply]
  rw [DoubleCoset.rel_iff, QuotientGroup.leftRel_apply, mem_sup_iff hc]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [hc a x, mul_assoc, inv_mul_cancel_left]
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [hc a x, mul_assoc, h, mul_inv_cancel_left]

theorem relIndex_split (hc : ∀ a b : A, a * b = b * a) (h u c : Subgroup A) (huc : u ≤ c) :
    u.relIndex c = (h ⊓ u).relIndex (h ⊓ c) * (h ⊔ u).relIndex (h ⊔ c) := by
  haveI : u.Normal := normal_of_comm hc u
  haveI : (h ⊔ u).Normal := normal_of_comm hc (h ⊔ u)
  have hM : (h ⊔ u) ⊓ c = (h ⊓ c) ⊔ u := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff hc h u).1 hx1
      have hpc : p ∈ c := by
        have := c.mul_mem hx2 (c.inv_mem (huc hq))
        rwa [mul_inv_cancel_right] at this
      exact (mem_sup_iff hc _ _).2 ⟨p, Subgroup.mem_inf.2 ⟨hp, hpc⟩, q, hq, rfl⟩
    · exact sup_le (inf_le_inf_right c le_sup_left) (le_inf le_sup_right huc)
  have e1 := Subgroup.relIndex_mul_relIndex (H := u) (K := (h ⊔ u) ⊓ c) (L := c)
    (le_inf le_sup_right huc) inf_le_right
  have e2 : ((h ⊔ u) ⊓ c).relIndex c = (h ⊔ u).relIndex (h ⊔ c) := by
    rw [Subgroup.inf_relIndex_right, ← Subgroup.relIndex_sup_right (H := c) (K := h ⊔ u)]
    congr 1
    apply le_antisymm
    · exact sup_le le_sup_right (sup_le le_sup_left (huc.trans le_sup_right))
    · exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
  have e3 : u.relIndex ((h ⊔ u) ⊓ c) = (h ⊓ u).relIndex (h ⊓ c) := by
    rw [hM, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right (H := u) (K := h ⊓ c)]
    congr 1
    apply le_antisymm
    · exact le_inf (inf_le_right.trans inf_le_left) inf_le_left
    · exact le_inf inf_le_right (inf_le_inf_left h huc)
  rw [← e1, e2, e3]

theorem card_split (h u c : Subgroup A) (huc : u ≤ c) :
    (h ⊓ u).relIndex (h ⊓ c) * Nat.card (h ⊓ u : Subgroup A) = Nat.card (h ⊓ c : Subgroup A) := by
  have hle : h ⊓ u ≤ h ⊓ c := inf_le_inf_left h huc
  have := Subgroup.card_mul_index ((h ⊓ u).subgroupOf (h ⊓ c))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at this
  rw [Subgroup.relIndex, mul_comm, this]

end GlobalTheory.DCIndex

namespace GlobalTheory.DCIndex

theorem card_inf_subgroupOf {G : Type} [Group G] (T H U : Subgroup G) (hUT : U ≤ T) :
    Nat.card (H.subgroupOf T ⊓ U.subgroupOf T : Subgroup T) = Nat.card (H ⊓ U : Subgroup G) := by
  have he : H.subgroupOf T ⊓ U.subgroupOf T = (H ⊓ U).subgroupOf T := by
    ext x; simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [he]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hUT)).toEquiv

theorem index_identity : ∀ {G : Type} [Group G] (T H U C : Subgroup G), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → U ≤ C → C ≤ T → U.relIndex C ≠ 0 → (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((U.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ U : Subgroup G) : ℂ) = (U.relIndex C : ℂ) * (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ C : Subgroup G) : ℂ) := by
  intro G _ T H U C hcomm hUC hCT hne
  have hc : ∀ a b : T, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  have hu'c' : U.subgroupOf T ≤ C.subgroupOf T := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hUC hx
  have hrel : (U.subgroupOf T).relIndex (C.subgroupOf T) = U.relIndex C :=
    Subgroup.relIndex_subgroupOf hCT
  rw [card_quot_eq_index hc, card_quot_eq_index hc, ← card_inf_subgroupOf T H U (hUC.trans hCT),
    ← card_inf_subgroupOf T H C hCT, ← hrel]
  rw [← hrel] at hne
  have hU := (Subgroup.relIndex_mul_index
    (sup_le_sup_left hu'c' (H.subgroupOf T))).symm
  have hsplit := relIndex_split hc (H.subgroupOf T) _ _ hu'c'
  have hcard := card_split (H.subgroupOf T) _ _ hu'c'
  rw [hU, hsplit, ← hcard]
  rw [hsplit] at hne
  have hs : (((H.subgroupOf T ⊓ U.subgroupOf T).relIndex (H.subgroupOf T ⊓ C.subgroupOf T) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (left_ne_zero_of_mul hne)
  push_cast
  rw [mul_assoc, mul_div_mul_left _ _ hs]

end GlobalTheory.DCIndex
