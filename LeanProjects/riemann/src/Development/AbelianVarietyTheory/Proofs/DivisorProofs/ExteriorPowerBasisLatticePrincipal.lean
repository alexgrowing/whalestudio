import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import ReciprocityTheory.DualLattices.WedgeNeZeroOfLinearIndependent
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem span_wedge_of_span_basis : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (N : ℕ) (b : Module.Basis (Fin N) C V), Module.finrank C (⋀[C]^N V) = 1 ∧ exteriorPower.ιMulti C N b ≠ 0 ∧ Submodule.span O {w : ⋀[C]^N V | ∃ x : Fin N → V, (∀ i, x i ∈ (Submodule.span O (Set.range b) : Set V)) ∧ w = exteriorPower.ιMulti C N x} = Submodule.span O {exteriorPower.ιMulti C N b} := by
  intro C _ O _ _ V _ _ _ _ N b
  haveI : Module.Finite C V := Module.Finite.of_basis b
  refine ⟨?_, ?_, ?_⟩
  · rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b, Fintype.card_fin, Nat.choose_self]
  · intro h
    apply ReciprocityTheory.PGsh.wedge_ne_zero_of_linearIndependent b.linearIndependent
    have := congrArg Subtype.val h
    simpa using this
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro w ⟨x, hx, rfl⟩
      obtain ⟨r, hr⟩ := ReciprocityTheory.PGsh.exists_wedge_eq_integral_smul (R := O) b.linearIndependent hx
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨r, ?_⟩
      apply Subtype.ext
      rw [Submodule.coe_smul_of_tower, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, hr,
        algebraMap_smul]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      apply Submodule.subset_span
      exact ⟨b, fun i => Submodule.subset_span ⟨i, rfl⟩, rfl⟩

end GlobalTheory
