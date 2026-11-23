import Mathlib
open Polynomial

namespace GlobalTheory.CommSemisimpleChars

open Classical in

theorem card_eq_of_sum_eq {H ι κ : Type} [Monoid H] [Fintype ι] [Fintype κ]
    (a : ι → (H →* ℂ)) (c : κ → (H →* ℂ)) (h : ∀ g, ∑ j, a j g = ∑ i, c i g) (ψ : H →* ℂ) :
    (Finset.univ.filter fun j => a j = ψ).card = (Finset.univ.filter fun i => c i = ψ).card := by
  classical
  let F : Finset (H →* ℂ) := insert ψ (Finset.univ.image a ∪ Finset.univ.image c)
  have li := linearIndependent_iff'.1 (linearIndependent_monoidHom H ℂ) F
    (fun φ => ((Finset.univ.filter fun j => a j = φ).card : ℂ) - (Finset.univ.filter fun i => c i = φ).card)
  have key : ∀ {τ : Type} [Fintype τ] (e : τ → (H →* ℂ)), (∀ t, e t ∈ F) →
      ∑ φ ∈ F, ((Finset.univ.filter fun t => e t = φ).card : ℂ) • (φ : H → ℂ) = ∑ t, (e t : H → ℂ) := by
    intro τ _ e he
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := F) (g := e) (fun t _ => he t)]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
  have hz : ∑ φ ∈ F, (((Finset.univ.filter fun j => a j = φ).card : ℂ) -
      (Finset.univ.filter fun i => c i = φ).card) • (φ : H → ℂ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [key a (fun j => by simp [F]), key c (fun i => by simp [F]), sub_eq_zero]
    funext g
    simp only [Finset.sum_apply]
    exact h g
  have := li hz ψ (Finset.mem_insert_self _ _)
  exact_mod_cast sub_eq_zero.1 this

end GlobalTheory.CommSemisimpleChars
