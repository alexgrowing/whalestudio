import Mathlib

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem relIndex_inf_eq_of_mem_mul : ∀ (G : Type) [Group G] (Γ K₁ K₂ : Subgroup G),
    (∀ k ∈ K₂, ∃ γ ∈ Γ, ∃ k' ∈ K₁ ⊓ K₂, k = γ * k') →
      (K₁ ⊓ Γ).relIndex (K₂ ⊓ Γ) = K₁.relIndex K₂ := by
  intro G _ Γ K₁ K₂ h
  unfold Subgroup.relIndex Subgroup.index
  let i : ↥(K₂ ⊓ Γ) → ↥K₂ := fun x => ⟨x.1, x.2.1⟩
  have key : ∀ a b : ↥(K₂ ⊓ Γ),
      (QuotientGroup.leftRel ((K₁ ⊓ Γ).subgroupOf (K₂ ⊓ Γ))) a b ↔
      (QuotientGroup.leftRel (K₁.subgroupOf K₂)) (i a) (i b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro H
      exact H.1
    · intro H
      exact ⟨H, (a⁻¹ * b).2.2⟩
  let f : ↥(K₂ ⊓ Γ) ⧸ (K₁ ⊓ Γ).subgroupOf (K₂ ⊓ Γ) → ↥K₂ ⧸ K₁.subgroupOf K₂ :=
    Quotient.map' i (fun a b H => (key a b).1 H)
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro x y
    induction x using Quotient.inductionOn' with | h a => ?_
    induction y using Quotient.inductionOn' with | h b => ?_
    intro H
    exact Quotient.sound' ((key a b).2 (Quotient.exact' H))
  · intro y
    induction y using Quotient.inductionOn' with | h k => ?_
    obtain ⟨γ, hγ, k', hk', e⟩ := h k.1 k.2
    have hγ2 : γ ∈ K₂ := by
      have : γ = k.1 * k'⁻¹ := by rw [e]; simp
      rw [this]
      exact K₂.mul_mem k.2 (K₂.inv_mem hk'.2)
    refine ⟨Quotient.mk'' ⟨γ, hγ2, hγ⟩, Quotient.sound' ?_⟩
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    have : ((((i ⟨γ, hγ2, hγ⟩)⁻¹ * k : ↥K₂)) : G) = k' := by
      simp [i, e]
    rw [this]
    exact hk'.1

end GlobalTheory.CompanionTheory.Ar.Cmp
