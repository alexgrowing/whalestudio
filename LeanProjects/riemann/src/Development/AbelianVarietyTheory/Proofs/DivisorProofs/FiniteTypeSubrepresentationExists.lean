import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
open GlobalTheory.LocFinIso

namespace GlobalTheory.FinSpanSub

theorem main : ∀ (G : Type) [Group G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (h1 : (1 : G) ∈ K) (hmul : ∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) (hst : ∀ k ∈ K, ∀ x ∈ D, ρ k x ∈ D) (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ), (∀ i, b i ∈ D) → (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) → ∃ W : Submodule (MonoidAlgebra ℂ (subK K h1 hmul)) (repD ρ D K h1 hmul hst).asModule, ∀ u, u ∈ W ↔ (((repD ρ D K h1 hmul hst).asModuleEquiv u : D) : V) ∈ Submodule.span ℂ (Set.range b) := by
  intro G _ K V _ _ ρ D h1 hmul hst m b A _hb hA
  have hstab : ∀ k ∈ K, ∀ x ∈ Submodule.span ℂ (Set.range b), ρ k x ∈ Submodule.span ℂ (Set.range b) := by
    intro k hk x hx
    have hle : Submodule.span ℂ (Set.range b) ≤ (Submodule.span ℂ (Set.range b)).comap (ρ k) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show ρ k (b j) ∈ Submodule.span ℂ (Set.range b)
      rw [hA k hk j]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact hle hx
  refine ⟨{ carrier := {u | (((repD ρ D K h1 hmul hst).asModuleEquiv u : D) : V) ∈ Submodule.span ℂ (Set.range b)}
            add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun u => Iff.rfl⟩
  · intro x y hx hy
    simp only [Set.mem_setOf_eq, map_add, Submodule.coe_add] at hx hy ⊢
    exact Submodule.add_mem _ hx hy
  · simp only [Set.mem_setOf_eq, map_zero, ZeroMemClass.coe_zero]
    exact Submodule.zero_mem _
  · intro a u hu
    simp only [Set.mem_setOf_eq] at hu ⊢
    rw [smul_val]
    exact Submodule.sum_mem _ fun κ _ => Submodule.smul_mem _ _ (hstab κ κ.2 _ hu)

end GlobalTheory.FinSpanSub
