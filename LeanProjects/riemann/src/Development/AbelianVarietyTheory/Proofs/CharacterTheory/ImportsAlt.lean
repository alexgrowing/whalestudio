import Mathlib

universe u_1 u_2

namespace GlobalTheory.UnimodularLatticeExistence

open Representation

theorem main : ∀ {G : Type u_1} [inst : Group G] {V : Type u_2} [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] (ρ : Representation ℂ G V), Representation.IsIrreducible ρ ↔ Nontrivial V ∧ ∀ (U : Submodule ℂ V), (∀ (g : G), ∀ v ∈ U, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro G _ V _ _ ρ
  have hbot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
  have htop : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
      apply Subrepresentation.toSubmodule_injective
      rw [hbot, htop]
      exact Subsingleton.elim _ _
    · intro U hU
      let σ : Subrepresentation ρ := ⟨U, fun g v hv => hU g v hv⟩
      rcases h.eq_bot_or_eq_top σ with h1 | h1
      · left
        have := congrArg Subrepresentation.toSubmodule h1
        exact this
      · right
        have := congrArg Subrepresentation.toSubmodule h1
        exact this
  · rintro ⟨hV, hU⟩
    haveI : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
      have := congrArg Subrepresentation.toSubmodule h
      rw [hbot, htop] at this
      exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this
    refine ⟨fun σ => ?_⟩
    rcases hU σ.toSubmodule (fun g v hv => σ.apply_mem_toSubmodule g hv) with h1 | h1
    · left
      apply Subrepresentation.toSubmodule_injective
      rw [h1, hbot]
    · right
      apply Subrepresentation.toSubmodule_injective
      rw [h1, htop]

end GlobalTheory.UnimodularLatticeExistence
