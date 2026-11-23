import Mathlib

open Polynomial

namespace GlobalTheory

theorem jets_mem_subalgebra_of_finiteType : ∀ (k A R : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (N : ℕ) (Δ : ℕ → A →ₗ[k] R), Δ 0 1 = 1 → (∀ l, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ p u * Δ (l - p) w)) →
 ∃ T : Finset R, ∀ S : Subalgebra k R, (∀ t ∈ T, t ∈ S) → ∀ l < N, ∀ u, Δ l u ∈ S := by
  intro k A R _ _ _ _ _ _ N Δ _ hL
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  refine ⟨(Finset.range N ×ˢ insert 1 s).image (fun x => Δ x.1 x.2), ?_⟩
  intro S hT l hl u
  have key : ∀ u ∈ Algebra.adjoin k (s : Set A), ∀ l < N, Δ l u ∈ S := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem x hx =>
      intro l hl
      exact hT _ (Finset.mem_image.2 ⟨(l, x), by simp [hl, Finset.mem_coe.1 hx], rfl⟩)
    | algebraMap c =>
      intro l hl
      rw [Algebra.algebraMap_eq_smul_one, map_smul]
      exact S.smul_mem (hT _ (Finset.mem_image.2 ⟨(l, 1), by simp [hl], rfl⟩)) c
    | add x y _ _ hx hy =>
      intro l hl
      rw [map_add]
      exact S.add_mem (hx l hl) (hy l hl)
    | mul x y _ _ hx hy =>
      intro l hl
      rw [hL]
      refine S.sum_mem (fun p hp => nsmul_mem (S.mul_mem (hx p ?_) (hy (l - p) ?_)) _)
      · have := Finset.mem_range.1 hp; omega
      · omega
  exact key u (hs ▸ Algebra.mem_top) l hl

end GlobalTheory
