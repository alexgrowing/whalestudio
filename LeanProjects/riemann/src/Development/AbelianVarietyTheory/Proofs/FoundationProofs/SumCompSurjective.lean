import Mathlib

namespace GlobalTheory.SumCompSurjective

open Finset

theorem sum_comp_surjective {G Q : Type} [AddCommGroup G] [AddCommGroup Q] [Fintype G] [Fintype Q]
    (π : G →+ Q) (hπ : Function.Surjective (⇑π : G → Q)) (g : Q → ℂ) :
    ∃ n : ℕ, 0 < n ∧ ∑ y : G, g (π y) = (n : ℂ) * ∑ q : Q, g q := by
  classical
  have hfib : ∀ q : Q, (univ.filter fun y : G => π y = q).card
      = (univ.filter fun y : G => π y = 0).card := by
    intro q
    obtain ⟨a, rfl⟩ := hπ q
    refine Finset.card_bij (fun y _ => y - a) ?_ ?_ ?_
    · intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      rw [map_sub, hy, sub_self]
    · intro y _ z _ h
      exact sub_left_injective h
    · intro z hz
      simp only [mem_filter, mem_univ, true_and] at hz
      refine ⟨z + a, ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and]
      rw [map_add, hz, zero_add]
  refine ⟨(univ.filter fun y : G => π y = 0).card, ?_, ?_⟩
  · exact Finset.card_pos.2 ⟨0, by simp⟩
  · rw [← Finset.sum_fiberwise (s := univ) (g := fun y : G => π y) (f := fun y => g (π y)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => g q) (fun y hy => by rw [(mem_filter.1 hy).2]),
      Finset.sum_const, hfib q, nsmul_eq_mul]

end GlobalTheory.SumCompSurjective
