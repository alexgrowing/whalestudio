import Mathlib
open Polynomial

namespace GlobalTheory

theorem exists_finite_transcendenceBasis_in_family :
    ∀ (k C : Type) [Field k] [Field C] [Algebra k C] (m : ℕ) (a : Fin m → C),
      ∃ (d : ℕ) (t : Fin d → C), AlgebraicIndependent k t ∧
        ∀ j, IsAlgebraic (IntermediateField.adjoin k (Set.range t)) (a j) := by
  intro k C _ _ _ m a
  classical
  have h0 : AlgebraicIndepOn k a (∅ : Set (Fin m)) :=
    algebraicIndependent_empty_type_iff.mpr (algebraMap k C).injective
  obtain ⟨s, hs⟩ := (Set.toFinite {s : Set (Fin m) | AlgebraicIndepOn k a s}).exists_maximal
    ⟨∅, h0⟩
  have hsi : AlgebraicIndepOn k a s := hs.prop
  let e : s ≃ Fin (Nat.card s) := Finite.equivFin s
  refine ⟨Nat.card s, fun i => a (e.symm i), ?_, ?_⟩
  · exact hsi.comp e.symm e.symm.injective
  · have hr : Set.range (fun i => a (e.symm i)) = a '' s := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, (e.symm i).2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨e ⟨y, hy⟩, by simp only [Equiv.symm_apply_apply]⟩
    intro j
    rw [hr]
    by_cases hj : j ∈ s
    · exact isAlgebraic_algebraMap
        (⟨a j, IntermediateField.subset_adjoin k _ ⟨j, hj, rfl⟩⟩ :
          IntermediateField.adjoin k (a '' s))
    · have hni : ¬ AlgebraicIndepOn k a (insert j s) := by
        intro h
        have hle : insert j s ≤ s := hs.2 h (Set.subset_insert j s)
        exact hj (hle (Set.mem_insert j s))
      rw [AlgebraicIndepOn.insert_iff hj] at hni
      have halg : IsAlgebraic (Algebra.adjoin k (a '' s)) (a j) := by
        by_contra hc
        exact hni ⟨hsi, hc⟩
      exact IntermediateField.isAlgebraic_adjoin_iff.mpr halg

end GlobalTheory
